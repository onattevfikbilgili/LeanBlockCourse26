#!/usr/bin/env -S uv run --quiet --script
# /// script
# requires-python = ">=3.11"
# ///
"""Generate OUTLINE.md from repo contents (slides, sections, exercise blocks)."""

import re
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
CODE_DIR = ROOT / "LeanBlockCourse26"
SLIDES_DIR = ROOT / "lecture-slides"
OUT = ROOT / "OUTLINE.md"

# Static part metadata: (directory_name, description)
# Only parts listed here appear in the outline.
PARTS = [
    ("P01_Introduction", "Why formalize maths? The tech stack: how to properly organize a formalization project."),
    ("P02_Logic", "Foundations of logic in Lean: what is a type and what does being classical vs. intuitionistic mean?"),
    ("P03_SetTheory", "Set theory in Lean: why you should rarely do set theory in Lean."),
    ("P04_TypeTheory", "Dependent type theory: where do the axioms live?"),
    ("P05_NaturalNumbers", "Natural numbers in Lean: why inductive types are so powerful."),
]

EXERCISE_RE = re.compile(r"^## .*[Ee]xercise", re.MULTILINE)
TITLE_RE = re.compile(r"^# (.+)$", re.MULTILINE)


def find_slides(part: str) -> Path | None:
    """Return path to slide PDF if it exists."""
    pdf = SLIDES_DIR / f"{part}.pdf"
    return pdf if pdf.exists() else None


def find_sections(part: str) -> list[tuple[str, str, int]]:
    """Return [(section_name, topic, exercise_count)] for a part."""
    part_dir = CODE_DIR / part
    if not part_dir.is_dir():
        return []

    sections = []
    for f in sorted(part_dir.glob("S*.lean")):
        name = f.stem
        text = f.read_text()

        # Extract topic from first `# Title` inside a doc comment
        topic = ""
        if m := TITLE_RE.search(text):
            topic = m.group(1).strip().rstrip("=").strip()

        # Count exercise blocks
        ex_count = len(EXERCISE_RE.findall(text))

        sections.append((name, topic, ex_count))

    return sections


def generate() -> str:
    lines = [
        "---",
        "title: Outline",
        "nav_order: 2",
        "---",
        "",
        "# Course Outline",
        "",
        "The course outline is still subject to change, but will roughly be as follows.",
    ]

    for part, description in PARTS:
        lines.append("")
        lines.append("---")
        lines.append("")
        lines.append(f"## {part}")
        lines.append("")
        lines.append(description)

        # Slides
        if pdf := find_slides(part):
            rel = pdf.relative_to(ROOT)
            lines.append("")
            lines.append(f"**Slides:** [{pdf.name}]({rel})")

        # Sections
        sections = find_sections(part)
        if not sections:
            continue

        has_exercises = any(ex > 0 for _, _, ex in sections)
        lines.append("")

        if has_exercises:
            lines.append("| Section | Topic | Exercises |")
            lines.append("|---------|-------|-----------|")
            for name, topic, ex in sections:
                ex_str = f"{ex} block{'s' if ex != 1 else ''}" if ex > 0 else "—"
                lines.append(f"| {name} | {topic} | {ex_str} |")
        else:
            lines.append("| Section | Topic |")
            lines.append("|---------|-------|")
            for name, topic, _ in sections:
                lines.append(f"| {name} | {topic} |")

    # Examination (static)
    lines.append("")
    lines.append("---")
    lines.append("")
    lines.append("## Examination")
    lines.append("")
    lines.append("Final exam and distribution of formalization projects for Master-level students.")
    lines.append("")

    return "\n".join(lines)


if __name__ == "__main__":
    content = generate()
    OUT.write_text(content)
    print(f"Generated {OUT.relative_to(ROOT)}")
