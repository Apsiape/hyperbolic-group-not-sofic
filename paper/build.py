"""Build the self-contained manuscript with three bounded pdflatex passes."""
from pathlib import Path
import shutil
import subprocess

ROOT = Path(__file__).resolve().parent
OUT = ROOT / "build"
OUT.mkdir(exist_ok=True)
for _ in range(3):
    run = subprocess.run(
        ["pdflatex", "-interaction=nonstopmode", "-halt-on-error",
         "-output-directory=build", "paper.tex"],
        cwd=ROOT, capture_output=True, text=True, errors="replace", timeout=300,
    )
    if run.returncode:
        print("\n".join(run.stdout.splitlines()[-45:]))
        raise SystemExit(run.returncode)
log = (OUT / "paper.log").read_text(errors="replace")
warnings = [line for line in log.splitlines() if any(s in line for s in (
    "undefined", "Overfull", "multiply defined", "Rerun to get"
))]
if warnings:
    print("\n".join(warnings))
    raise SystemExit("Unresolved manuscript build warnings; inspect build/paper.log.")
shutil.copy2(OUT / "paper.pdf", ROOT / "paper.pdf")
print("Built paper.pdf; no undefined references, duplicate labels, or overfull boxes.")
