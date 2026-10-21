#!/usr/bin/env python3
"""Pack or safely restore a portable paper bundle using bounded tracked parts."""

import argparse
import gzip
import hashlib
import json
from pathlib import Path
import shutil
import tarfile
import tempfile

MAX_PART_BYTES = 32 * 1024 * 1024


class TransportError(ValueError):
    pass


def require(condition, message):
    if not condition:
        raise TransportError(message)


def sha(path):
    value = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            value.update(block)
    return value.hexdigest()


def relative_name(name):
    path = Path(name)
    require(isinstance(name, str) and name and not path.is_absolute() and
            ".." not in path.parts and "\\" not in name and path.as_posix() == name,
            "unsafe transport member")
    return path


def validate_payload(directory, expected_bundle):
    receipt = directory / "bundle.json"
    require(receipt.is_file() and not receipt.is_symlink() and sha(receipt) == expected_bundle,
            "bundle receipt hash mismatch")
    record = json.loads(receipt.read_bytes())
    inventory = record.get("inventory", {})
    require(isinstance(inventory, dict) and inventory, "bundle has no payload inventory")
    expected = {"bundle.json", *inventory}
    actual = set()
    for path in directory.rglob("*"):
        require(not path.is_symlink(), "symlink in bundle payload")
        if path.is_file():
            actual.add(path.relative_to(directory).as_posix())
    require(actual == expected, "bundle payload members differ from inventory")
    for name, item in inventory.items():
        path = directory / relative_name(name)
        require(path.is_file() and path.stat().st_size == item["bytes"] and sha(path) == item["sha256"],
                "bundle payload hash or size mismatch: " + name)
    return sorted(expected)


def pack_bundle(directory, output, *, part_bytes=MAX_PART_BYTES):
    directory, output = Path(directory).resolve(), Path(output).absolute()
    require(type(part_bytes) is int and 0 < part_bytes <= MAX_PART_BYTES, "invalid part size")
    require(directory.is_dir() and (not output.exists() and not output.is_symlink()), "transport destination must be new")
    require(not output.resolve().is_relative_to(directory), "transport cannot be inside its bundle")
    bundle_hash = sha(directory / "bundle.json")
    names = validate_payload(directory, bundle_hash)
    output.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory(prefix=".evidence-transport-", dir=output.parent) as temporary:
        stage = Path(temporary)
        archive_path = stage / "evidence.tar.gz"
        uncompressed = 0
        with archive_path.open("wb") as raw, gzip.GzipFile(filename="", mode="wb", fileobj=raw, mtime=0) as zipped:
            with tarfile.open(fileobj=zipped, mode="w", format=tarfile.PAX_FORMAT) as archive:
                for name in names:
                    path = directory / name
                    member = tarfile.TarInfo(name)
                    member.size, member.mode, member.mtime = path.stat().st_size, 0o644, 0
                    uncompressed += member.size
                    with path.open("rb") as content:
                        archive.addfile(member, content)
        parts = []
        with archive_path.open("rb") as stream:
            while data := stream.read(part_bytes):
                name = f"evidence.part-{len(parts):05d}"
                (stage / name).write_bytes(data)
                parts.append({"file": name, "bytes": len(data), "sha256": hashlib.sha256(data).hexdigest()})
        record = {"schema_version": 1, "format": "split_gzip_tar", "bundle_sha256": bundle_hash,
                  "archive_sha256": sha(archive_path), "archive_bytes": archive_path.stat().st_size,
                  "uncompressed_bytes": uncompressed, "part_bytes": part_bytes, "parts": parts}
        archive_path.unlink()
        (stage / "transport.json").write_text(json.dumps(record, indent=2, sort_keys=True) + "\n")
        validate_payload(directory, bundle_hash)
        require((not output.exists() and not output.is_symlink()), "transport destination appeared during packing")
        stage.rename(output)
    return record


def unpack_bundle(receipt, destination, *, expected_receipt_sha256, expected_bundle_sha256):
    receipt, destination = Path(receipt).resolve(), Path(destination).absolute()
    require(receipt.is_file() and sha(receipt) == expected_receipt_sha256, "transport receipt hash mismatch")
    record = json.loads(receipt.read_bytes())
    require(record.get("schema_version") == 1 and record.get("format") == "split_gzip_tar",
            "unsupported evidence transport")
    require(record.get("bundle_sha256") == expected_bundle_sha256, "unexpected transported bundle")
    require(type(record.get("part_bytes")) is int and 0 < record["part_bytes"] <= MAX_PART_BYTES,
            "invalid transport part limit")
    require(type(record.get("uncompressed_bytes")) is int and record["uncompressed_bytes"] > 0,
            "invalid uncompressed byte bound")
    require((not destination.exists() and not destination.is_symlink()), "bundle destination must be new")
    parts = record.get("parts")
    require(isinstance(parts, list) and parts, "transport has no parts")
    destination.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory(prefix=".evidence-unpack-", dir=destination.parent) as temporary:
        temporary = Path(temporary)
        archive_path = temporary / "evidence.tar.gz"
        with archive_path.open("wb") as archive:
            for index, item in enumerate(parts):
                require(item.get("file") == f"evidence.part-{index:05d}", "invalid transport part sequence")
                path = receipt.parent / relative_name(item["file"])
                require(type(item.get("bytes")) is int and 0 < item["bytes"] <= record["part_bytes"],
                        "transport part exceeds its bound")
                require(path.is_file() and not path.is_symlink() and path.stat().st_size == item["bytes"] and
                        sha(path) == item["sha256"], "transport part changed or missing: " + item["file"])
                with path.open("rb") as content:
                    shutil.copyfileobj(content, archive)
        require(archive_path.stat().st_size == record.get("archive_bytes") and
                sha(archive_path) == record.get("archive_sha256"), "transport archive hash or size mismatch")
        stage = temporary / "bundle"
        stage.mkdir()
        seen, total = set(), 0
        try:
            with tarfile.open(archive_path, "r:gz") as archive:
                for member in archive:
                    name = relative_name(member.name)
                    require(member.isfile() and member.name not in seen, "nonregular or duplicate transport member")
                    seen.add(member.name)
                    total += member.size
                    require(total <= record["uncompressed_bytes"], "transport exceeds uncompressed byte bound")
                    target = stage / name
                    target.parent.mkdir(parents=True, exist_ok=True)
                    with archive.extractfile(member) as content, target.open("xb") as output:
                        shutil.copyfileobj(content, output)
                    require(target.stat().st_size == member.size, "truncated transport member")
        except (tarfile.TarError, OSError, EOFError) as error:
            raise TransportError("invalid compressed evidence archive") from error
        require(total == record["uncompressed_bytes"], "uncompressed transport size mismatch")
        validate_payload(stage, expected_bundle_sha256)
        require((not destination.exists() and not destination.is_symlink()), "bundle destination appeared during extraction")
        stage.rename(destination)
    return destination


def restore_configured_bundle(config, root):
    root = Path(root).resolve()
    name = config.get("evidence_bundle")
    require(isinstance(name, str) and name, "transport requires a configured evidence bundle")
    destination = Path(name)
    destination = destination if destination.is_absolute() else root / destination
    keys = ["evidence_transport", "evidence_transport_sha256"]
    present = [config.get(key) is not None for key in keys]
    require(not any(present) or all(present), "incomplete evidence transport configuration")
    if destination.is_dir():
        return destination
    require(all(present), "evidence bundle is absent; configure its checked transport")
    receipt = Path(config["evidence_transport"])
    receipt = receipt if receipt.is_absolute() else root / receipt
    return unpack_bundle(receipt, destination,
                         expected_receipt_sha256=config["evidence_transport_sha256"],
                         expected_bundle_sha256=config.get("evidence_bundle_sha256"))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    subcommands = parser.add_subparsers(dest="command", required=True)
    pack = subcommands.add_parser("pack")
    pack.add_argument("bundle", type=Path)
    pack.add_argument("--output", type=Path, required=True)
    unpack = subcommands.add_parser("unpack")
    unpack.add_argument("receipt", type=Path)
    unpack.add_argument("--output", type=Path, required=True)
    unpack.add_argument("--receipt-sha256", required=True)
    unpack.add_argument("--bundle-sha256", required=True)
    args = parser.parse_args()
    try:
        if args.command == "pack":
            record = pack_bundle(args.bundle, args.output)
            print(json.dumps({"transport": str(args.output / "transport.json"),
                              "transport_sha256": sha(args.output / "transport.json"),
                              "bundle_sha256": record["bundle_sha256"], "parts": len(record["parts"])}))
        else:
            print(unpack_bundle(args.receipt, args.output, expected_receipt_sha256=args.receipt_sha256,
                                expected_bundle_sha256=args.bundle_sha256))
    except (TransportError, OSError, KeyError, TypeError, json.JSONDecodeError) as error:
        raise SystemExit("evidence transport: " + str(error)) from error


if __name__ == "__main__":
    main()
