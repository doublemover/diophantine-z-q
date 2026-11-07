from pathlib import Path
import gzip

root = Path(__file__).resolve().parents[1]
for compressed in sorted(root.rglob("*.json.gz")):
    target = compressed.with_suffix("")
    data = gzip.decompress(compressed.read_bytes())
    if target.exists() and target.read_bytes() != data:
        raise SystemExit(f"Refusing to overwrite changed file: {target}")
    target.write_bytes(data)
print("Expanded compressed inputs.")
