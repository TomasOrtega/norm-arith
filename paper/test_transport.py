"""Synthetic transport fixtures; no Lean or manuscript measurements are produced."""

import hashlib
import io
import json
from pathlib import Path
import shutil
import tarfile
import tempfile
import unittest

import evidence_transport as transport


def digest(data):
    return hashlib.sha256(data).hexdigest()


class TransportTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        self.bundle = self.root / "bundle"
        self.bundle.mkdir()
        self.payload = {"records/synthetic.jsonl": b'{"synthetic":true}\n' * 20,
                        "proof/synthetic.olean": b"SYNTHETIC TEST BYTES, NOT A LEAN PROOF"}
        for name, data in self.payload.items():
            path = self.bundle / name
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes(data)
        record = {"inventory": {name: {"sha256": digest(data), "bytes": len(data)}
                                 for name, data in self.payload.items()}}
        (self.bundle / "bundle.json").write_text(json.dumps(record) + "\n")
        self.bundle_hash = digest((self.bundle / "bundle.json").read_bytes())

    def pack(self, name="transport", part_bytes=64):
        output = self.root / name
        return output, transport.pack_bundle(self.bundle, output, part_bytes=part_bytes)

    def unpack(self, output, record, name="unpacked"):
        return transport.unpack_bundle(output / "transport.json", self.root / name,
            expected_receipt_sha256=digest((output / "transport.json").read_bytes()),
            expected_bundle_sha256=self.bundle_hash)

    def replace_archive(self, output, record, entries):
        data = io.BytesIO()
        with tarfile.open(fileobj=data, mode="w:gz") as archive:
            for name, content, kind in entries:
                member = tarfile.TarInfo(name)
                member.type = kind
                member.size = len(content) if kind == tarfile.REGTYPE else 0
                member.linkname = "../escape" if kind == tarfile.SYMTYPE else ""
                archive.addfile(member, io.BytesIO(content) if member.size else None)
        raw = data.getvalue()
        part = output / "evidence.part-00000"
        part.write_bytes(raw)
        record.update(parts=[{"file": part.name, "bytes": len(raw), "sha256": digest(raw)}],
                      archive_bytes=len(raw), archive_sha256=digest(raw),
                      part_bytes=transport.MAX_PART_BYTES,
                      uncompressed_bytes=sum(len(content) for _, content, _ in entries))
        (output / "transport.json").write_text(json.dumps(record) + "\n")

    def test_deterministic_transport(self):
        left, a = self.pack("left")
        right, b = self.pack("right")
        self.assertEqual(a, b)
        self.assertEqual((left / "transport.json").read_bytes(), (right / "transport.json").read_bytes())
        for part in a["parts"]:
            self.assertEqual((left / part["file"]).read_bytes(), (right / part["file"]).read_bytes())

    def test_roundtrip_without_original_bundle(self):
        output, record = self.pack()
        self.assertGreater(len(record["parts"]), 1)
        shutil.rmtree(self.bundle)
        destination = self.unpack(output, record)
        for name, data in self.payload.items():
            self.assertEqual((destination / name).read_bytes(), data)

    def test_corrupt_or_missing_part_is_rejected(self):
        for missing in [False, True]:
            with self.subTest(missing=missing):
                output, record = self.pack("missing" if missing else "corrupt")
                part = output / record["parts"][0]["file"]
                part.unlink() if missing else part.write_bytes(b"changed")
                with self.assertRaisesRegex(transport.TransportError, "part"):
                    self.unpack(output, record)
                self.assertFalse((self.root / "unpacked").exists())

    def test_unsafe_symlink_duplicate_and_extra_members_are_rejected(self):
        original = [("bundle.json", (self.bundle / "bundle.json").read_bytes(), tarfile.REGTYPE)]
        original += [(name, data, tarfile.REGTYPE) for name, data in self.payload.items()]
        variants = {"traversal": original + [("../escape", b"bad", tarfile.REGTYPE)],
                    "symlink": original + [("link", b"", tarfile.SYMTYPE)],
                    "duplicate": original + [original[1]],
                    "extra": original + [("unexpected", b"bad", tarfile.REGTYPE)]}
        for name, entries in variants.items():
            with self.subTest(name=name):
                output, record = self.pack(name)
                self.replace_archive(output, record, entries)
                with self.assertRaises(transport.TransportError):
                    self.unpack(output, record)
                self.assertFalse((self.root / "unpacked").exists())

    def test_coherent_transport_cannot_change_inventory_bound_payload(self):
        output, record = self.pack()
        entries = [("bundle.json", (self.bundle / "bundle.json").read_bytes(), tarfile.REGTYPE)]
        entries += [(name, b"changed" if name.endswith(".olean") else data, tarfile.REGTYPE)
                    for name, data in self.payload.items()]
        self.replace_archive(output, record, entries)
        with self.assertRaisesRegex(transport.TransportError, "payload"):
            self.unpack(output, record)

    def test_expected_receipt_and_bundle_hashes_are_required(self):
        output, record = self.pack()
        for receipt_hash, bundle_hash in [("0" * 64, self.bundle_hash),
                                           (digest((output / "transport.json").read_bytes()), "0" * 64)]:
            with self.subTest(bundle=bundle_hash):
                with self.assertRaises(transport.TransportError):
                    transport.unpack_bundle(output / "transport.json", self.root / "unpacked",
                        expected_receipt_sha256=receipt_hash, expected_bundle_sha256=bundle_hash)

    def test_configured_bootstrap_needs_no_original_bundle(self):
        output, record = self.pack()
        shutil.rmtree(self.bundle)
        config = {"evidence_bundle": "bundle", "evidence_bundle_sha256": self.bundle_hash,
                  "evidence_transport": "transport/transport.json",
                  "evidence_transport_sha256": digest((output / "transport.json").read_bytes())}
        restored = transport.restore_configured_bundle(config, self.root)
        self.assertEqual(restored, self.bundle.resolve())
        self.assertEqual((restored / "proof/synthetic.olean").read_bytes(), self.payload["proof/synthetic.olean"])

    def test_absent_bundle_requires_complete_transport_configuration(self):
        shutil.rmtree(self.bundle)
        for extra in [{}, {"evidence_transport": "missing.json"}]:
            with self.subTest(extra=extra):
                config = {"evidence_bundle": "bundle", "evidence_bundle_sha256": self.bundle_hash, **extra}
                with self.assertRaisesRegex(transport.TransportError, "transport"):
                    transport.restore_configured_bundle(config, self.root)

    def test_dangling_destination_symlinks_are_not_replaced(self):
        output = self.root / "blocked-transport"
        output.symlink_to(self.root / "missing-output")
        with self.assertRaises(transport.TransportError):
            transport.pack_bundle(self.bundle, output)
        self.assertTrue(output.is_symlink())
        output, record = self.pack()
        destination = self.root / "unpacked"
        destination.symlink_to(self.root / "missing-bundle")
        with self.assertRaises(transport.TransportError):
            self.unpack(output, record)
        self.assertTrue(destination.is_symlink())

    def test_part_limit_and_existing_destinations(self):
        with self.assertRaises(transport.TransportError):
            self.pack(part_bytes=transport.MAX_PART_BYTES + 1)
        output, record = self.pack()
        destination = self.root / "unpacked"
        destination.mkdir()
        (destination / "keep").write_text("keep")
        with self.assertRaises(transport.TransportError):
            self.unpack(output, record)
        self.assertEqual((destination / "keep").read_text(), "keep")


if __name__ == "__main__":
    unittest.main()
