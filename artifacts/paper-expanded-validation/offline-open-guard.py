import atexit, json, os, sys
from pathlib import Path
root = os.environ["BLOCKED_ORIGINAL_ROOT"]
counts = {"python_pid": os.getpid(), "open_events": 0, "blocked_original_reads": 0, "blocked_lean_launches": 0}
def audit(event, args):
    if event == "open":
        counts["open_events"] += 1
        try:
            name = os.fsdecode(os.fspath(args[0]))
        except TypeError:
            return
        if name == root or name.startswith(root + os.sep):
            counts["blocked_original_reads"] += 1
            raise PermissionError("Original workspace byte access denied in offline validation: " + name)
    if event == "subprocess.Popen" and Path(os.fsdecode(args[0])).name in {"lake", "lean", "elan"}:
        counts["blocked_lean_launches"] += 1
        raise PermissionError("Lean launch denied in offline validation")
sys.addaudithook(audit)
@atexit.register
def record():
    Path(os.environ["OFFLINE_AUDIT_DIRECTORY"], str(os.getpid()) + ".json").write_text(json.dumps(counts, sort_keys=True) + "\n")
