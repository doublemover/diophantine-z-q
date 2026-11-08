"""Run the unchanged, hash-bound Version13 inventory controls on a minimal fixture.

Only the original checker's whole-repository temporary copy is adapted. Every
file actually inspected by its positive validation is copied and the relocated
fixture is positively validated before the original filesystem negative controls.
No frozen inventory, verifier, acceptance record or mathematical source is edited.
"""
from pathlib import Path
from types import SimpleNamespace
import hashlib
import importlib.util
import json
import shutil

ROOT = Path(__file__).resolve().parents[1]
SOURCE = ROOT / 'docs/manuscript-revisions/version13/validate-applications.py'
EXPECTED = '082933cd6d4063f5e9c77bb951b53b05e37a333832172429740b1634e4cdce87'


def main():
    if hashlib.sha256(SOURCE.read_bytes()).hexdigest() != EXPECTED:
        raise ValueError('Reviewed Version13 inventory checker changed')
    spec = importlib.util.spec_from_file_location('version13_original_inventory', SOURCE)
    original = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(original)
    inventory = SOURCE.parent / 'APPLICATIONS.json'
    data = json.loads(inventory.read_text(encoding='utf-8'))
    contract = json.loads((SOURCE.parent / 'validation-schema.json').read_text(encoding='utf-8'))
    result = original.validate(data, ROOT, contract)
    files = result['checkedFiles']

    def copy_validated_fixture(source, destination):
        if Path(source).resolve() != ROOT or Path(destination).exists():
            raise ValueError('Unexpected temporary-copy request')
        destination = Path(destination)
        destination.mkdir(parents=True)
        for relative in files:
            src = (ROOT / relative).resolve()
            if not src.is_relative_to(ROOT) or not src.is_file():
                raise ValueError('Unsafe or missing validated source')
            target = destination / relative
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(src, target)
        relocated = original.validate(data, destination, contract)
        if relocated != result:
            raise ValueError('Relocated fixture changed validation coverage')
        return destination

    original_shutil = original.shutil
    original.shutil = SimpleNamespace(copytree=copy_validated_fixture)
    try:
        result['negativeControls'] = original.controls(data, ROOT, contract)
    finally:
        original.shutil = original_shutil
    if len(result['negativeControls']) != 10:
        raise ValueError('Incomplete original negative controls')
    result['inventorySha256'] = original.sha(inventory)
    result['fixtureBytes'] = sum((ROOT / p).stat().st_size for p in files)
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
