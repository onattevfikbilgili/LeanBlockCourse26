#!/usr/bin/env -S uv run --quiet --script
# /// script
# requires-python = ">=3.11"
# ///
"""Generate OUTLINE.md and inject announcements into HOME.md."""

import re
from dataclasses import dataclass, field
from datetime import date, timedelta
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
CODE_DIR = ROOT / "LeanBlockCourse26"
SLIDES_DIR = ROOT / "lecture-slides"
OUT = ROOT / "OUTLINE.md"
HOME = ROOT / "HOME.md"
README = ROOT / "README.md"

GITHUB_BLOB = "https://github.com/FordUniver/LeanBlockCourse26/blob/main"

# Static part metadata: (directory_name, description)
# Only parts listed here appear in the outline.
PARTS = [
    ("P01_Introduction", "Why formalize maths? The tech stack: how to properly organize a formalization project."),
    ("P02_Logic", "Foundations of logic in Lean: what is a type and what does being classical vs. intuitionistic mean?"),
    ("P03_SetTheory", "Set theory in Lean: why you should rarely do set theory in Lean."),
    ("P04_TypeTheory", "Dependent type theory: where do the axioms live?"),
    ("P05_NaturalNumbers", "Natural numbers in Lean: why inductive types are so powerful."),
]

TITLE_RE = re.compile(r"^# (.+)$", re.MULTILINE)
BLOCK_RE = re.compile(r"^## .*[Ee]xercise.*$", re.MULTILINE)
BLOCK_LABEL_RE = re.compile(r"B(\d+)")
EXERCISE_RE = re.compile(r"^-- Exercise (.+)$", re.MULTILINE)


@dataclass
class Exercise:
    label: str
    line: int
    description: str = ""


@dataclass
class ExerciseBlock:
    heading: str
    line: int
    exercises: list[Exercise] = field(default_factory=list)


@dataclass
class Section:
    name: str
    topic: str
    rel_path: str
    blocks: list[ExerciseBlock] = field(default_factory=list)


def line_of(text: str, pos: int) -> int:
    """Convert byte offset to 1-based line number."""
    return text[:pos].count("\n") + 1


def github_url(rel_path: str, line: int | None = None) -> str:
    url = f"{GITHUB_BLOB}/{rel_path}"
    if line is not None:
        url += f"#L{line}"
    return url


def find_slides(part: str) -> Path | None:
    pdf = SLIDES_DIR / f"{part}.pdf"
    return pdf if pdf.exists() else None


def find_sections(part: str) -> list[Section]:
    part_dir = CODE_DIR / part
    if not part_dir.is_dir():
        return []

    sections = []
    for f in sorted(part_dir.glob("S*.lean")):
        text = f.read_text()
        lines = text.splitlines()
        rel_path = f.relative_to(ROOT)

        # Extract topic from first `# Title` inside a doc comment
        topic = ""
        if m := TITLE_RE.search(text):
            topic = m.group(1).strip().rstrip("=").strip()

        # Find exercise blocks and their positions
        block_matches = list(BLOCK_RE.finditer(text))
        blocks: list[ExerciseBlock] = []

        for i, bm in enumerate(block_matches):
            block_line = line_of(text, bm.start())
            heading = bm.group(0).removeprefix("## ")

            # Region: from block heading to next block heading or EOF
            start = bm.end()
            end = block_matches[i + 1].start() if i + 1 < len(block_matches) else len(text)
            region = text[start:end]
            region_offset = start

            # Find individual exercises in this region
            exercises: list[Exercise] = []
            for em in EXERCISE_RE.finditer(region):
                ex_line = line_of(text, region_offset + em.start())
                label = em.group(1).strip()

                # Extract description from following `-- ` comment lines
                desc_parts = []
                for subsequent in lines[ex_line:]:  # lines after the exercise label
                    if subsequent.startswith("-- ") and not subsequent.startswith("-- Exercise "):
                        desc_parts.append(subsequent[3:].strip())
                    else:
                        break
                description = " ".join(desc_parts)

                exercises.append(Exercise(label=label, line=ex_line, description=description))

            blocks.append(ExerciseBlock(heading=heading, line=block_line, exercises=exercises))

        sections.append(Section(
            name=f.stem,
            topic=topic,
            rel_path=str(rel_path),
            blocks=blocks,
        ))

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

    # Slides table (all parts with available PDFs)
    slide_rows = []
    for part, _ in PARTS:
        if pdf := find_slides(part):
            rel = pdf.relative_to(ROOT)
            slide_rows.append(f"| `{part}` | [{pdf.name}]({rel}) |")
    if slide_rows:
        lines.append("")
        lines.append("## Slides")
        lines.append("")
        lines.append("| Part | PDF |")
        lines.append("|------|-----|")
        lines.extend(slide_rows)

    for part, description in PARTS:
        lines.append("")
        lines.append("---")
        lines.append("")
        lines.append(f"## `{part}`")
        lines.append("")
        lines.append(description)

        # Sections
        sections = find_sections(part)
        if not sections:
            continue

        has_exercises = any(sec.blocks for sec in sections)
        lines.append("")
        if has_exercises:
            lines.append("| Section | Topic | Exercises |")
            lines.append("|---------|-------|-----------|")
        else:
            lines.append("| Section | Topic |")
            lines.append("|---------|-------|")
        for sec in sections:
            link = f"[`{sec.name}`]({github_url(sec.rel_path)})"
            if has_exercises:
                if sec.blocks:
                    def block_label(b: ExerciseBlock, i: int) -> str:
                        if m := BLOCK_LABEL_RE.search(b.heading):
                            return f"B{int(m.group(1)):02d}"
                        return f"B{i + 1:02d}"

                    block_links = " \\| ".join(
                        f"[`{block_label(b, i)}`]({github_url(sec.rel_path, b.line)})"
                        for i, b in enumerate(sec.blocks)
                    )
                else:
                    block_links = "—"
                lines.append(f"| {link} | {sec.topic} | {block_links} |")
            else:
                lines.append(f"| {link} | {sec.topic} |")

    # Examination (static)
    lines.append("")
    lines.append("---")
    lines.append("")
    lines.append("## Examination")
    lines.append("")
    lines.append("Final exam and distribution of formalization projects for Master-level students.")
    lines.append("")

    return "\n".join(lines)


ANNOUNCE_RE = re.compile(
    r"^## Announcements\n(.*?)(?=\n## |\Z)",
    re.MULTILINE | re.DOTALL,
)
ANNOUNCE_DATE_RE = re.compile(r"^\s*-\s+\*\*(\d{4}-\d{2}-\d{2}):\*\*")
BEGIN_MARKER = "<!-- begin announcements -->"
END_MARKER = "<!-- end announcements -->"

RECENT_DAYS = 3


def parse_announcement(line: str) -> tuple[date | None, str]:
    """Extract date and body text from an announcement bullet line."""
    if m := ANNOUNCE_DATE_RE.match(line):
        d = date.fromisoformat(m.group(1))
        # Strip the `- **YYYY-MM-DD:** ` prefix to get the body
        body = line[m.end():].strip()
        return d, body
    return None, line.lstrip("- ").strip()


def inline_md_to_html(text: str) -> str:
    """Convert basic inline markdown (**bold** and `code`) to HTML."""
    text = re.sub(r"\*\*(.+?)\*\*", r"<strong>\1</strong>", text)
    text = re.sub(r"`(.+?)`", r"<code>\1</code>", text)
    return text


def format_date_label(d: date) -> str:
    """Format date as 'Mon, Mar 3' inside a just-the-docs label pill."""
    # e.g. "Mon, Mar 3"
    text = d.strftime("%a, %b %-d")
    return f'<span class="label label-yellow">{text}</span>'


def render_announcement(d: date | None, body: str) -> str:
    """Render a single announcement as an HTML paragraph with date label."""
    html_body = inline_md_to_html(body)
    if d is not None:
        return f"<p>{format_date_label(d)} {html_body}</p>"
    return f"<p>{html_body}</p>"


def inject_announcements() -> None:
    """Extract ## Announcements from README.md and inject into HOME.md.

    Recent announcements (within RECENT_DAYS) are shown in a highlighted
    callout at the top. Older ones are collapsed in a <details> block.
    """
    readme = README.read_text()
    m = ANNOUNCE_RE.search(readme)
    if not m:
        return

    bullets = [l for l in m.group(1).strip().splitlines() if l.strip()]
    if not bullets:
        return

    cutoff = date.today() - timedelta(days=RECENT_DAYS)
    recent: list[tuple[date | None, str]] = []
    older: list[tuple[date | None, str]] = []
    for line in bullets:
        d, body = parse_announcement(line)
        if d is not None and d < cutoff:
            older.append((d, body))
        else:
            recent.append((d, body))

    parts: list[str] = []

    if recent:
        parts.append('<blockquote class="highlight">')
        for d, body in recent:
            parts.append(render_announcement(d, body))
        parts.append("</blockquote>")
        parts.append("")

    if older:
        parts.append("<details>")
        summary = "Older announcements" if recent else "Announcements"
        parts.append(f"<summary>{summary}</summary>")
        parts.append('<blockquote class="highlight">')
        for d, body in older:
            parts.append(render_announcement(d, body))
        parts.append("</blockquote>")
        parts.append("</details>")
        parts.append("")

    body = "\n".join(parts)

    home = HOME.read_text()
    begin = home.find(BEGIN_MARKER)
    end = home.find(END_MARKER)
    if begin == -1 or end == -1:
        return

    home = home[:begin + len(BEGIN_MARKER)] + "\n" + body + home[end:]
    HOME.write_text(home)


if __name__ == "__main__":
    content = generate()
    OUT.write_text(content)
    print(f"Generated {OUT.relative_to(ROOT)}")

    inject_announcements()
    print(f"Injected announcements into {HOME.relative_to(ROOT)}")
