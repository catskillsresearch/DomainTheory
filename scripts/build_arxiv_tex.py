#!/usr/bin/env python3
r"""Convert arxiv_with_code.md to arxiv.tex (PDF build).

Pipeline:
  1. Drop the GitHub-only navigation preamble from ``arxiv_with_code.md``.
  2. Lift the `## Abstract` section into a LaTeX \begin{abstract}.
  3. Keep the Palomar-archive appendix as a ``\\section`` of file summaries
     with hyperlinked subsection titles; insert \\appendix before it.
  4. Strip manual section numbers so LaTeX does the numbering.
  5. Replace fenced Lean/math/bash with \\lstinputlisting blocks; render mermaid to PNG.
  6. Inject AI model-card acknowledgements; pandoc -> LaTeX; splice placeholders.
  7. Emit a single ``arxiv.tex`` for one-shot latexmk (pdfLaTeX; arXiv AutoTeX).
"""

from __future__ import annotations

import os
import re
import shutil
import subprocess
import sys
import textwrap
from pathlib import Path

from PIL import Image

ROOT = Path(__file__).resolve().parent.parent
SCRIPTS = Path(__file__).resolve().parent
sys.path.insert(0, str(SCRIPTS))
from ai_model_cards import inject_model_cards
from lean_listing_sanitize import chunk_line_ranges, sanitize_lean_for_arxiv

SRC = Path(os.environ.get("ARXIV_WITH_CODE", ROOT / "arxiv_with_code.md"))
OUT = Path(os.environ.get("ARXIV_TEX", ROOT / "arxiv.tex"))
PREAMBLE = SCRIPTS / "tex_preamble_arxiv.tex"
LISTINGS_DIR = ROOT / "lean-listings"
FIGURES_DIR = ROOT / "figures"
PUPPETEER_CONFIG = SCRIPTS / "puppeteer-config.json"
MERMAID_CONFIG = SCRIPTS / "mermaid-config.json"
LISTING_CHUNK_LINES = 400
_WRITTEN_LISTINGS: set[Path] = set()

# Letter (8.5x11) content box under fullpage ≈ 6.5in × 9in; leave room for caption.
LETTER_FIG_MAX_WIDTH_IN = 6.5
LETTER_FIG_MAX_HEIGHT_IN = 8.0
LETTER_FIG_DPI = 150

GITHUB_URL = r"https://github.com/catskillsresearch/DomainTheory"
# CMU SCS tech-report front matter (same authors / style as archive/scott1964).
# Update REPORT_NUMBER when the library assigns an official id.
REPORT_NUMBER = "CMU-CS-26-140"
REPORT_DATE = "October 2026"
PDF_AUTHORS = "Lars Warren Ericson; Dana S. Scott; Vijay D'Silva; Brian Milnes"
KEYWORDS = (
    "Lean 4; formal verification; domain theory; continuous lattices; "
    "neighbourhood systems; information systems; Scott topology"
)
PDF_KEYWORDS = (
    "Lean 4, formal verification, domain theory, continuous lattices, "
    "neighbourhood systems, information systems"
)


def find_chrome() -> str | None:
    env = os.environ.get("PUPPETEER_EXECUTABLE_PATH")
    if env and Path(env).exists():
        return env
    for name in ("google-chrome", "google-chrome-stable", "chromium", "chromium-browser"):
        path = shutil.which(name)
        if path:
            return path
    return None


def fit_png_for_letter(png_path: Path) -> None:
    """Downscale a PNG so it fits an 8.5×11in content box at ``LETTER_FIG_DPI``."""
    max_w = int(LETTER_FIG_MAX_WIDTH_IN * LETTER_FIG_DPI)
    max_h = int(LETTER_FIG_MAX_HEIGHT_IN * LETTER_FIG_DPI)
    with Image.open(png_path) as im:
        w, h = im.size
        if w <= max_w and h <= max_h:
            return
        scale = min(max_w / w, max_h / h)
        new_size = (max(1, int(w * scale)), max(1, int(h * scale)))
        fitted = im.resize(new_size, Image.Resampling.LANCZOS)
        fitted.save(png_path, optimize=True)


def render_mermaid(code: str, idx: int) -> str:
    FIGURES_DIR.mkdir(parents=True, exist_ok=True)
    mmd_path = FIGURES_DIR / f"figure-{idx:03d}.mmd"
    png_path = FIGURES_DIR / f"figure-{idx:03d}.png"
    pdf_path = FIGURES_DIR / f"figure-{idx:03d}.pdf"
    code_stripped = code.strip() + "\n"
    if pdf_path.is_file():
        pdf_path.unlink()
    cached = (
        mmd_path.is_file()
        and png_path.is_file()
        and mmd_path.read_text(encoding="utf-8") == code_stripped
    )
    if not cached:
        mmd_path.write_text(code_stripped, encoding="utf-8")

        mmdc = shutil.which("mmdc")
        if not mmdc:
            raise RuntimeError(
                "mermaid-cli (mmdc) not found; install with "
                "`npm install -g @mermaid-js/mermaid-cli`"
            )
        env = os.environ.copy()
        chrome = find_chrome()
        if chrome:
            env["PUPPETEER_EXECUTABLE_PATH"] = chrome
        # Raster PNG for arXiv (embedded PDF figures are rejected).
        cmd = [mmdc, "-i", str(mmd_path), "-o", str(png_path), "-b", "white", "-s", "2"]
        if MERMAID_CONFIG.is_file():
            cmd += ["-c", str(MERMAID_CONFIG)]
        if PUPPETEER_CONFIG.is_file():
            cmd += ["-p", str(PUPPETEER_CONFIG)]
        proc = subprocess.run(cmd, env=env, capture_output=True, text=True, check=False)
        if proc.returncode != 0 or not png_path.is_file():
            sys.stderr.write(proc.stdout + "\n" + proc.stderr + "\n")
            sys.stderr.write(
                f"warning: mmdc failed on figure {idx}; embedding diagram source as a listing\n"
            )
            rel_listing, _ = write_listing(code_stripped, f"mermaid-figure-{idx:03d}.mmd")
            return f"LISTING:{rel_listing}"
    fit_png_for_letter(png_path)
    return png_path.relative_to(ROOT).as_posix()


def extract_title() -> str:
    path = ROOT / "arxiv.md"
    if not path.is_file():
        return "Domain Theory in Lean 4"
    for line in path.read_text(encoding="utf-8").splitlines():
        stripped = line.strip()
        if stripped.startswith("<!--") or not stripped:
            continue
        title = stripped[2:].strip() if stripped.startswith("# ") else stripped
        title = re.sub(r"\*([^*]+)\*", r"\\emph{\1}", title)
        return title
    return "Domain Theory in Lean 4"


TITLE = extract_title()

GITHUB_INLINE_MATH = re.compile(r"\$`([^`\n]+?)`\$")
# Pandoc markdown does not treat ``\(...\)`` as math; convert before pandoc.
LATEX_INLINE_MATH = re.compile(r"\\\((.+?)\\\)")
LATEX_DISPLAY_MATH = re.compile(r"\\\[(.+?)\\\]", re.DOTALL)
HTML_COMMENT = re.compile(r"<!--.*?-->", re.DOTALL)
FENCE_RE = re.compile(r"^```([^\n]*)\n(.*?)^```\s*$", re.MULTILINE | re.DOTALL)
MANUAL_SECTION_NUM = re.compile(r"^(#{1,6})[ \t]+\d+(?:\.\d+)*\.?[ \t]+", re.MULTILINE)
NARRATIVE_MARKER = "# Narrative (from arxiv.md)"
# After normalize_appendix_headings: `### DomainTheory/...File.lean` precedes each fence.
LEAN_FILE_HEADING_RE = re.compile(
    r"^###\s+(DomainTheory(?:\.lean|/[\w./-]+\.lean))\s*$"
)
APPENDIX_HEADING_RE = re.compile(
    r"^##\s+Appendix\s+[A-Z]\s*[-\u2013\u2014]+\s*(.+)$", re.MULTILINE
)
# ASCII fallbacks for combining-mark sequences and emoji that `\newunicodechar` cannot
# handle cleanly (accents stack backwards in LaTeX; emoji have no single-glyph textcomp
# equivalent worth a new package dependency). Order matters: longer sequences first.
PROSE_ASCII_FALLBACKS: tuple[tuple[str, str], ...] = (
    ("\u26a0\ufe0f", "Warning:"),  # WARNING SIGN + VARIATION SELECTOR-16
    ("\u26a0", "Warning:"),  # bare WARNING SIGN
    ("w\u20d7", "w-vec"),  # w + COMBINING RIGHT ARROW ABOVE
    ("\u03c3\u20d7", "sigma-vec"),  # sigma + COMBINING RIGHT ARROW ABOVE
    ("\u2003", " "),  # EM SPACE
    ("\u2002", " "),  # EN SPACE
    ("\u00a0", " "),  # NO-BREAK SPACE
    ("\u202f", " "),  # NARROW NO-BREAK SPACE
    ("f\u0302", "f-hat"),  # f + COMBINING CIRCUMFLEX ACCENT
    ("\u039b\u0302", "Lambda-hat"),  # Lambda + COMBINING CIRCUMFLEX ACCENT
    ("\u2705", r"\ensuremath{\checkmark}"),  # WHITE HEAVY CHECK MARK
    ("\u2611", r"\ensuremath{\checkmark}"),  # BALLOT BOX WITH CHECK
    ("\u2610", "[ ]"),  # BALLOT BOX (Composer checklist unchecked)
)
# Supplementary-plane letters cannot be \newunicodechar'd under pdfLaTeX. Apply
# these on the emitted TeX so pandoc does not escape the replacement.
PDFLATEX_UNICODE_FIXES: tuple[tuple[str, str], ...] = (
    ("\U0001d49f", r"\ensuremath{\mathcal{D}}"),  # 𝒟
    ("\U0001d4af", r"\ensuremath{\mathcal{T}}"),  # 𝒯
    ("\U0001d509", r"\ensuremath{\mathfrak{F}}"),  # 𝔉
    ("\U0001d50a", r"\ensuremath{\mathfrak{G}}"),  # 𝔊
    ("\U0001d546", r"\ensuremath{\mathbb{O}}"),  # 𝕆
)


def apply_prose_ascii_fallbacks(text: str) -> str:
    for src, dst in PROSE_ASCII_FALLBACKS:
        text = text.replace(src, dst)
    # Remaining COMBINING RIGHT ARROW ABOVE (e.g. 1⃗, 01⃗) after explicit σ⃗/w⃗ rules.
    text = re.sub(r"(.)\u20d7", r"\1-vec", text)
    return text


# Box / geometric / punctuation glyphs that sometimes leak outside listings.
_BOX_ASCII: tuple[tuple[str, str], ...] = (
    ("│", "|"),
    ("─", "-"),
    ("━", "-"),
    ("├", "+"),
    ("┤", "+"),
    ("┬", "+"),
    ("┴", "+"),
    ("┼", "+"),
    ("┌", "+"),
    ("┐", "+"),
    ("└", "+"),
    ("┘", "+"),
    ("╭", "+"),
    ("╮", "+"),
    ("╰", "+"),
    ("╯", "+"),
    ("║", "|"),
    ("═", "="),
    ("╔", "+"),
    ("╗", "+"),
    ("╚", "+"),
    ("╝", "+"),
    ("╠", "+"),
    ("╣", "+"),
    ("╱", "/"),
    ("╲", "/"),
    ("○", "o"),
    ("∿", "~"),
    ("\u2212", "-"),  # MINUS SIGN
    ("\u2013", "-"),  # EN DASH (safe in verbatim; prose often wants this too)
    ("\u2217", "*"),  # ASTERISK OPERATOR
    ("\u00b7", "."),  # MIDDLE DOT
    ("\u2026", "..."),  # HORIZONTAL ELLIPSIS
    ("\u2080", "0"),  # subscripts that appear in ascii-art trees
    ("\u2081", "1"),
    ("\u2082", "2"),
    ("\u2083", "3"),
    ("\u2084", "4"),
    ("\u2085", "5"),
    ("\u2086", "6"),
    ("\u2087", "7"),
    ("\u2088", "8"),
    ("\u2089", "9"),
    ("\u208a", "+"),
    ("\u208b", "-"),
)


def apply_pdflatex_unicode_fixes(text: str) -> str:
    """Replace glyphs pdfLaTeX cannot declare (SMP letters / box art) in TeX output."""
    for src, dst in PDFLATEX_UNICODE_FIXES:
        text = text.replace(src, dst)
    for src, dst in _BOX_ASCII:
        text = text.replace(src, dst)
    # Any remaining supplementary-plane characters become a safe ASCII placeholder.
    def _smp(m: re.Match[str]) -> str:
        ch = m.group(0)
        return f"[U+{ord(ch):04X}]"

    text = re.sub(r"[\U00010000-\U0010FFFF]", _smp, text)
    # Scrub leftover box / block / geometric shapes that break T1 listings/prose.
    return re.sub(r"[\u2500-\u257F\u2580-\u259F\u25A0-\u25FF]", "?", text)


_LEAN_HREF_RE = re.compile(r"\]\(([^)]+\.lean)\)")


def canon_lean_hrefs_in_markdown(md: str) -> str:
    """Use repo-relative ``DomainTheory/...`` targets so PDF file links resolve."""
    by_name: dict[str, list[str]] = {}
    for path in (ROOT / "DomainTheory").rglob("*.lean"):
        rel = path.relative_to(ROOT).as_posix()
        by_name.setdefault(path.name, []).append(rel)

    def repl(m: re.Match[str]) -> str:
        href = m.group(1)
        if href.startswith("DomainTheory/"):
            return m.group(0)
        name = Path(href).name
        cands = by_name.get(name, [])
        if len(cands) == 1:
            return f"]({cands[0]})"
        return m.group(0)

    return _LEAN_HREF_RE.sub(repl, md)


def github_math_to_tex(text: str) -> str:
    text = GITHUB_INLINE_MATH.sub(r"$\1$", text)
    text = LATEX_INLINE_MATH.sub(r"$\1$", text)
    text = LATEX_DISPLAY_MATH.sub(r"$$\1$$", text)
    return text


def strip_html_comments(text: str) -> str:
    return HTML_COMMENT.sub("", text)


def strip_manual_section_numbers(text: str) -> str:
    return MANUAL_SECTION_NUM.sub(r"\1 ", text)


def drop_github_nav(text: str) -> str:
    for marker in (NARRATIVE_MARKER, "# Narrative + Lean source (from arxiv.md)"):
        idx = text.find(marker)
        if idx != -1:
            return text[idx + len(marker) :].lstrip("\n")
    return text


def normalize_appendix_headings(text: str) -> str:
    """Demote the Palomar-archive appendix to a section heading."""
    text = re.sub(
        r"^##\s+Appendix\.\s+Lean sources in the Palomar archive\s*$",
        "## Lean sources in the Palomar archive",
        text,
        flags=re.MULTILINE,
    )
    text = re.sub(
        r"^#\s+Appendix A: Complete Lean source\s*$",
        "## Lean sources in the Palomar archive",
        text,
        flags=re.MULTILINE,
    )
    return APPENDIX_HEADING_RE.sub(lambda m: f"## {m.group(1)}", text)


def demote_inventory_headings(text: str) -> str:
    """Turn `#### Exercise 2.1` inventory rows into bold text, not LaTeX subsubsections.

    The chronological narrative has 300+ such headings; pdfLaTeX's subsubsection counter
    overflows at 255.

    A blank line must follow the bold text: pandoc's markdown reader (unlike CommonMark)
    does not let a bullet list interrupt a paragraph, so without it every immediately
    following `* **Mathematical Target:**` / `* **Lean File:**` / `* **Proof Notes:**`
    block renders as a run-on paragraph with literal `*` characters instead of a proper
    itemized list.
    """
    return re.sub(r"^#### (.+)$", r"**\1**\n", text, flags=re.MULTILINE)


def extract_abstract(text: str) -> tuple[str, str]:
    m = re.search(r"^##\s+Abstract\s*\n(.*?)(?=^##\s)", text, re.DOTALL | re.MULTILINE)
    if not m:
        return "", text
    abstract_block = m.group(1).strip()
    # CMU front-matter abstract is prose only; leave diagrams / fences in the body.
    parts = re.split(
        r"\n(?=\*\*Dependency diagram\.\*\*|^```)",
        abstract_block,
        maxsplit=1,
        flags=re.MULTILINE,
    )
    abstract_md = parts[0].strip()
    leftover = parts[1].strip() if len(parts) > 1 else ""
    body = text[: m.start()]
    if leftover:
        body += leftover + "\n\n"
    body += text[m.end() :]
    return abstract_md, body


CAPTION_COMMENT_RE = re.compile(
    r"<!--\s*mermaid-caption:\s*(.+?)\s*-->\s*$", re.IGNORECASE
)


def extract_mermaid_captions(text: str) -> list[str]:
    """Caption each ```mermaid block from an explicit comment or nearest heading."""
    captions: list[str] = []
    for m in re.finditer(r"^```mermaid\s*$", text, re.MULTILINE):
        prefix = text[: m.start()]
        heading = None
        explicit = None
        for line in reversed(prefix.splitlines()):
            stripped = line.strip()
            if not stripped:
                continue
            cm = CAPTION_COMMENT_RE.match(stripped)
            if cm:
                explicit = cm.group(1).strip()
                break
            hm = re.match(r"^#{2,4}\s+(.+)$", stripped)
            if hm:
                heading = hm.group(1).strip()
                break
        if explicit:
            captions.append(explicit.rstrip(".") + ".")
        elif heading and heading.startswith("Lecture "):
            captions.append(f"Lean module dependencies for {heading}.")
        elif heading and "chapter" in heading.lower():
            captions.append(heading.rstrip(".") + ".")
        elif heading:
            captions.append(f"{heading}.")
        else:
            captions.append(f"Module dependency diagram {len(captions) + 1}.")
    return captions


def figure_latex(rel_path: str, caption: str, label: str) -> str:
    """Numbered figure at the markdown source position (no float drift)."""
    cap = caption.replace("&", "\\&")
    return (
        "\\begin{figure}[H]\n"
        "\\centering\n"
        f"\\includegraphics[width=\\linewidth,height=0.78\\textheight,keepaspectratio]"
        f"{{{rel_path}}}\n"
        f"\\caption{{{cap}}}\n"
        f"\\label{{{label}}}\n"
        "\\end{figure}\n"
    )


def listing_figure_latex(listing: str, caption: str, label: str) -> str:
    """Fallback numbered figure when mermaid rasterization fails."""
    cap = caption.replace("&", "\\&")
    return (
        "\\begin{figure}[H]\n"
        "\\centering\n"
        "\\begin{minipage}{\\linewidth}\n"
        f"\\lstinputlisting[style=leanbox]{{{listing}}}\n"
        "\\end{minipage}\n"
        f"\\caption{{{cap} (diagram source; PNG rasterization failed.)}}\n"
        f"\\label{{{label}}}\n"
        "\\end{figure}\n"
    )


def write_listing(code: str, listing_name: str) -> tuple[str, int]:
    LISTINGS_DIR.mkdir(parents=True, exist_ok=True)
    source = sanitize_lean_for_arxiv(code.rstrip("\n"))
    listing_path = LISTINGS_DIR / listing_name
    write_if_changed(listing_path, source + "\n")
    _WRITTEN_LISTINGS.add(listing_path.resolve())
    rel_path = listing_path.relative_to(ROOT).as_posix()
    return rel_path, (len(source.splitlines()) if source else 0)


def prune_stale_listings() -> None:
    if not LISTINGS_DIR.is_dir():
        return
    for path in LISTINGS_DIR.iterdir():
        if path.is_file() and path.resolve() not in _WRITTEN_LISTINGS:
            path.unlink()


_LEAN_MD_LINK_RE = re.compile(
    r"(?:\n|^)\*\*\[([^\]]+\.lean)\]\(([^)]+\.lean)\)\*\*\s*$"
)


def lean_file_href(repo_rel: str) -> str:
    """GitHub blob URL for a repo-relative ``.lean`` path."""
    rel = repo_rel.lstrip("./")
    return f"{GITHUB_URL}/blob/main/{rel}"


def tex_escape_texttt(s: str) -> str:
    """Escape characters that are special inside ``\\texttt{...}``."""
    return (
        s.replace("\\", "\\textbackslash{}")
        .replace("_", "\\_")
        .replace("#", "\\#")
        .replace("%", "\\%")
        .replace("&", "\\&")
        .replace("{", "\\{")
        .replace("}", "\\}")
    )


def lean_block_latex(
    code: str,
    listing_name: str,
    *,
    link_label: str | None = None,
    link_href: str | None = None,
) -> str:
    rel_path, line_count = write_listing(code, listing_name)
    ranges = chunk_line_ranges(line_count, LISTING_CHUNK_LINES)

    # Prefer the markdown citation label/href; fall back to the listing basename.
    label = link_label or Path(listing_name).name
    href = lean_file_href(link_href) if link_href else lean_file_href(
        listing_name if listing_name.startswith("DomainTheory/") else f"DomainTheory/{listing_name}"
    )
    header = (
        "\\vspace{0.5\\baselineskip}\n"
        f"\\noindent\\href{{{href}}}{{\\texttt{{{tex_escape_texttt(label)}}}}}"
        "\\par\\vspace{0.25\\baselineskip}\n"
    )

    parts: list[str] = [header]
    for first, last in ranges:
        if first == 1 and last == line_count:
            parts.append(
                f"\\lstinputlisting[style=leanbox]{{{rel_path}}}\n"
                "\\vspace{0.5\\baselineskip}\n\n"
            )
        else:
            # Chunked listings: filename once above; subsequent chunks need no label.
            if first != 1:
                parts.append("\\vspace{0.25\\baselineskip}\n")
            parts.append(
                f"\\lstinputlisting[style=leanbox,firstline={first},lastline={last}]"
                f"{{{rel_path}}}\n\n"
            )
    return "".join(parts)


def extract_lean_titles(text: str) -> dict[str, str]:
    """Map each ```lean fence to its module path from the preceding ``### path`` heading."""
    titles: dict[str, str] = {}
    lean_starts = [m.start() for m in re.finditer(r"^```lean\s*$", text, re.MULTILINE)]
    for idx, pos in enumerate(lean_starts):
        prefix = text[:pos].rstrip("\n")
        module = None
        for line in reversed(prefix.splitlines()[-6:]):
            m = LEAN_FILE_HEADING_RE.match(line.strip())
            if m:
                module = m.group(1)
                break
        titles[f"LEANINCLUDE{idx:03d}"] = module or f"module-{idx + 1}"
    return titles


def replace_fences(
    text: str, mermaid_captions: list[str] | None = None
) -> tuple[str, dict[str, str]]:
    lean_titles = extract_lean_titles(text)
    if mermaid_captions is None:
        mermaid_captions = extract_mermaid_captions(text)
    placeholders: dict[str, str] = {}
    lean_idx = 0
    other_idx = 0
    mermaid_idx = 0

    # Walk fences left-to-right so a preceding ``**[file.lean](path)**`` can be
    # consumed into the listing header (\\noindent\\href) instead of surviving
    # as a duplicate markdown link.
    out: list[str] = []
    last = 0
    for match in FENCE_RE.finditer(text):
        prefix = text[last : match.start()]
        lang = match.group(1).strip().lower()
        body = match.group(2)
        if lang == "lean":
            key = f"LEANINCLUDE{lean_idx:03d}"
            module = lean_titles.get(key, f"module-{lean_idx}")
            lean_idx += 1
            safe_name = module.replace("/", "-")
            if not safe_name.endswith(".lean"):
                safe_name += ".lean"
            link_label: str | None = None
            link_href: str | None = None
            lm = _LEAN_MD_LINK_RE.search(prefix)
            if lm and prefix[lm.end() :].strip() == "":
                link_label = Path(lm.group(1)).name
                link_href = lm.group(2)
                prefix = prefix[: lm.start()].rstrip() + "\n\n"
            elif module.endswith(".lean") and "/" in module:
                # ### DomainTheory/.../File.lean heading (inline lean mode).
                link_label = Path(module).name
                link_href = module
            placeholders[key] = lean_block_latex(
                body,
                safe_name,
                link_label=link_label or Path(safe_name).name,
                link_href=link_href,
            )
            out.append(prefix)
            out.append(f"\n\n{key}\n\n")
        elif lang == "math":
            key = f"MATHINCLUDE{other_idx:03d}"
            other_idx += 1
            placeholders[key] = f"\\[\n{body.strip()}\n\\]\n"
            out.append(prefix)
            out.append(f"\n\n{key}\n\n")
        elif lang == "mermaid":
            key = f"FIGINCLUDE{other_idx:03d}"
            rel_path = render_mermaid(body, mermaid_idx)
            caption = (
                mermaid_captions[mermaid_idx]
                if mermaid_idx < len(mermaid_captions)
                else f"Module dependency diagram {mermaid_idx + 1}"
            )
            label = f"fig:mermaid-{mermaid_idx:03d}"
            mermaid_idx += 1
            other_idx += 1
            if rel_path.startswith("LISTING:"):
                listing = rel_path.removeprefix("LISTING:")
                placeholders[key] = listing_figure_latex(listing, caption, label)
            else:
                placeholders[key] = figure_latex(rel_path, caption, label)
            out.append(prefix)
            out.append(f"\n\n{key}\n\n")
        else:
            key = f"CODEINCLUDE{other_idx:03d}"
            rel_path, _ = write_listing(body, f"snippet-{other_idx:03d}.txt")
            other_idx += 1
            placeholders[key] = f"\\lstinputlisting[style=leanbox]{{{rel_path}}}\n"
            out.append(prefix)
            out.append(f"\n\n{key}\n\n")
        last = match.end()
    out.append(text[last:])
    return "".join(out), placeholders


def inject_bibliography(text: str) -> str:
    """Replace the References section body with BibTeX processing commands."""
    m = re.search(r"^##\s+References\s*$", text, re.MULTILINE)
    if not m:
        raise RuntimeError("missing ## References; needed for BibTeX bibliography")
    # Keep the heading for pandoc → \\section{References}; drop any stub prose.
    # Everything after References is the bibliography (end of document).
    return (
        text[: m.end()]
        + "\n\n"
        + "\\nocite{*}\n"
        + "\\bibliographystyle{unsrt}\n"
        + "\\bibliography{references}\n"
    )


def pandoc_to_latex(markdown: str, shift: bool = True) -> str:
    cmd = [
        "pandoc",
        "-f",
        "markdown+tex_math_dollars+raw_tex+smart",
        "-t",
        "latex",
        "--wrap=none",
        "--no-highlight",
    ]
    if shift:
        cmd += ["--shift-heading-level-by=-1"]
    proc = subprocess.run(cmd, input=markdown, text=True, capture_output=True, check=False)
    if proc.returncode != 0:
        print(proc.stderr, file=sys.stderr)
        raise RuntimeError("pandoc failed")
    return proc.stdout


def inject_placeholders(latex: str, placeholders: dict[str, str]) -> str:
    out = latex
    for key, value in placeholders.items():
        patterns = [
            key,
            f"\\emph{{{key}}}",
            f"\\text{{{key}}}",
            f"\\passthrough{{\\lstinline!{key}!}}",
        ]
        for pat in patterns:
            if pat in out:
                out = out.replace(pat, value)
                break
        else:
            out = out.replace(key, value)
    return out


_MATH_REGION = re.compile(
    r"(\\\(.+?\\\)|\\\[.+?\\\]|"
    r"\$\$.+?\$\$|"
    r"(?<!\\)(?<!\$)\$(?!\$).+?(?<!\\)(?<!\$)\$(?!\$))",
    re.DOTALL,
)
_MATH_FONT_TO_TEXT = (
    ("mathbf", "textbf"),
    ("mathrm", "textrm"),
    ("mathit", "textit"),
    ("mathsf", "textsf"),
    ("mathtt", "texttt"),
)


def _math_fonts_outside_math(latex: str) -> str:
    """Map ``\\mathbf`` etc. to text-mode cmds only outside math regions.

    A global replace breaks constructs like ``\\(\\mathbf{\\times}\\)`` because
    ``\\times`` is illegal in ``\\textbf``.
    """
    parts = _MATH_REGION.split(latex)
    out: list[str] = []
    for i, part in enumerate(parts):
        if i % 2 == 1:
            # Inside math: keep math fonts; only remap unsupported script font.
            out.append(part.replace("\\mathscr{", "\\mathcal{"))
            continue
        for math_cmd, text_cmd in _MATH_FONT_TO_TEXT:
            part = re.sub(rf"\\{math_cmd}\{{", rf"\\{text_cmd}{{", part)
        part = part.replace("\\mathscr{", "\\mathcal{")
        out.append(part)
    return "".join(out)


def _unescape_pandoc_dollar_signs(latex: str) -> str:
    """Restore math delimiters Pandoc escaped in text mode only.

    Unparsed inline ``$...$`` becomes ``\\$...\\$`` outside math; TeX needs ``$...$``.
    Leave ``\\$`` untouched inside math (e.g. ``\\mathbf{\\$}`` in ``.english`` prose).
    """
    parts = _MATH_REGION.split(latex)
    out: list[str] = []
    for i, part in enumerate(parts):
        if i % 2 == 1:
            out.append(part)
            continue
        out.append(part.replace("\\$", "$"))
    return "".join(out)


def cleanup_pandoc_latex(latex: str) -> str:
    latex = latex.replace("\\pandocbounded{", "{")
    latex = _unescape_pandoc_dollar_signs(latex)
    latex = re.sub(r"\\tightlist\n", "", latex)
    # Pandoc's `\textquotesingle{}` inside `\texttt{...}` can recurse until
    # TeX's input stack overflows (e.g. Lean files named `insert_comm'.lean`).
    latex = latex.replace("\\textquotesingle{}", "'")
    latex = latex.replace("\\textquotesingle", "'")
    latex = _math_fonts_outside_math(latex)
    for cmd in ("section", "subsection", "subsubsection", "paragraph"):
        latex = re.sub(
            rf"(\\{cmd}\{{)\d+(?:\.\d+)*\.?\s+",
            r"\1",
            latex,
        )
    latex = re.sub(
        r"\\section\{Appendix A\. Lean source index\}",
        "",
        latex,
    )
    latex = re.sub(
        r"\\section\{Appendix A: Complete Lean source\}",
        r"\\section{Lean sources in the Palomar archive}",
        latex,
    )
    latex = re.sub(
        r"\\section\{Complete Lean source\}",
        r"\\section{Lean sources in the Palomar archive}",
        latex,
    )
    latex = re.sub(
        r"\\section\{Appendix\. Lean sources in the Palomar archive\}",
        r"\\section{Lean sources in the Palomar archive}",
        latex,
    )
    latex = re.sub(r"\n{3,}", "\n\n", latex)
    return latex


def insert_appendix_command(latex: str) -> str:
    marker = r"\section{Lean sources in the Palomar archive}"
    if marker not in latex:
        # Tree-compiled documents have no Palomar appendix.
        return latex
    return latex.replace(marker, r"\appendix" + "\n" + marker, 1)


def insert_front_matter_lists(latex: str) -> str:
    """Table of contents and list of figures after CMU front matter (unnumbered)."""
    block = (
        "{\\pagestyle{empty}\n"
        "\\tableofcontents\n"
        "\\clearpage\n"
        "\\listoffigures\n"
        "\\clearpage\n"
        "\\ifthenelse{\\isodd{\\value{page}}}{}{\\mbox{}\\clearpage}\n"
        "}\n"
        "\\pagestyle{plain}\n\n"
    )
    return block + latex


def build_document(preamble: str, title_page: str, body: str) -> str:
    return preamble + "\n\n" + title_page + "\n\n" + body + "\n\n\\end{document}\n"


def write_if_changed(path: Path, content: str) -> bool:
    """Write ``path`` only when content differs; return True if the file was updated."""
    if path.is_file() and path.read_text(encoding="utf-8") == content:
        return False
    path.write_text(content, encoding="utf-8")
    return True


def cleanup_abstract_latex(latex: str) -> str:
    """Keep the abstract LaTeX-safe: ASCII plus standard LaTeX escapes."""
    latex = latex.replace("\\pandocbounded{", "{")
    latex = _unescape_pandoc_dollar_signs(latex)
    latex = latex.replace("\\textbf{{[}", "\\textbf{[")
    latex = latex.replace("\\texttt{{[}", "\\texttt{[")
    latex = latex.replace("{]}}", "]}")
    latex = re.sub(r"\\tightlist\n", "", latex)
    latex = re.sub(r"\\begin\{center\}\\rule\{.*?\}\\end\{center\}\s*", "", latex, flags=re.DOTALL)
    return latex


def embed_cmu_abstract(abstract_latex: str) -> str:
    """Prepare abstract body for cmu-titlepage2's \\abstract / \\gdef storage.

    cmu-titlepage2's \\abstract is not \\long, so blank lines (\\par) are
    forbidden. ``\\gdef\\@abstract{#1}`` also treats ``#`` as a parameter
    marker, so every ``#`` in the body must be doubled.
    """
    body = abstract_latex.strip()
    # Single paragraph for the non-long \\abstract command.
    body = re.sub(r"\s*\n\s*", " ", body)
    return body.replace("#", "##")


def build_title_page(abstract_latex: str) -> str:
    abstract_body = embed_cmu_abstract(abstract_latex)
    return textwrap.dedent(
        f"""
        \\title{{{TITLE}}}

        \\author{{
          Lars Warren Ericson$^\\dagger$, Dana S. Scott, Vijay D'Silva$^\\ddagger$,\\\\
          Brian Milnes$^\\S$
        }}
        \\disclaimer{{$^\\dagger$ Catskills Research Company, $^\\ddagger$ Google Research, $^\\S$ Unaffiliated}}

        \\date{{{REPORT_DATE}}}
        \\trnumber{{{REPORT_NUMBER}}}
        \\keywords{{{KEYWORDS}}}
        \\abstract{{
        {abstract_body}
        }}
        \\hypersetup{{
          pdftitle={{{TITLE}}},
          pdfauthor={{{PDF_AUTHORS}}},
          pdfsubject={{Carnegie Mellon University School of Computer Science Technical Report {REPORT_NUMBER}}},
          pdfkeywords={{{PDF_KEYWORDS}}}
        }}

        \\begin{{document}}

        \\maketitle
        """
    ).strip()


def main() -> int:
    if not SRC.is_file():
        print(
            f"error: missing {SRC}; run scripts/generate_arxiv_with_code.sh first",
            file=sys.stderr,
        )
        return 1
    if not PREAMBLE.is_file():
        print(f"error: missing {PREAMBLE}", file=sys.stderr)
        return 1

    for d in (LISTINGS_DIR, FIGURES_DIR):
        d.mkdir(parents=True, exist_ok=True)
    _WRITTEN_LISTINGS.clear()

    raw = SRC.read_text(encoding="utf-8")
    body = drop_github_nav(raw)
    mermaid_captions = extract_mermaid_captions(body)
    body = apply_prose_ascii_fallbacks(body)
    body = inject_model_cards(body)
    body = inject_bibliography(body)
    body = strip_html_comments(body)
    body = normalize_appendix_headings(body)
    abstract_md, body = extract_abstract(body)
    body = strip_manual_section_numbers(body)
    # Tree-compiled notes use #### for nested subsections; only demote the old
    # inventory-style headings when the source is a hand-written arxiv.md.
    if "compile_md_tree.py" not in raw:
        body = demote_inventory_headings(body)
    body = github_math_to_tex(body)
    body = canon_lean_hrefs_in_markdown(body)
    body, placeholders = replace_fences(body, mermaid_captions)
    prune_stale_listings()
    for stale_pdf in FIGURES_DIR.glob("*.pdf"):
        stale_pdf.unlink()

    latex_body = pandoc_to_latex(body, shift=True)
    latex_body = inject_placeholders(latex_body, placeholders)
    latex_body = cleanup_pandoc_latex(latex_body)
    latex_body = insert_front_matter_lists(latex_body)
    latex_body = insert_appendix_command(latex_body)

    abstract_latex = pandoc_to_latex(github_math_to_tex(abstract_md), shift=False) if abstract_md else ""
    abstract_latex = cleanup_abstract_latex(abstract_latex)

    preamble = PREAMBLE.read_text(encoding="utf-8")
    title_page = build_title_page(abstract_latex)
    document = build_document(preamble, title_page, latex_body)
    # Only rewrite the document body: the preamble's \newunicodechar lines must
    # keep their SMP code points intact.
    body_start = document.find(r"\begin{document}")
    if body_start == -1:
        raise RuntimeError("missing \\begin{document} in assembled TeX")
    head, body = document[:body_start], document[body_start:]
    body = apply_pdflatex_unicode_fixes(body)
    leftover = sorted({ch for ch in body if ord(ch) > 0xFFFF})
    if leftover:
        shown = ", ".join(f"U+{ord(ch):04X}" for ch in leftover)
        raise RuntimeError(f"arxiv.tex body still has supplementary-plane characters: {shown}")
    document = head + body
    changed = write_if_changed(OUT, document)
    n_listings = sum(1 for p in LISTINGS_DIR.iterdir() if p.is_file()) if LISTINGS_DIR.is_dir() else 0
    n_figures = sum(1 for p in FIGURES_DIR.glob("*.png"))
    note = "updated" if changed else "unchanged"
    try:
        out_label = OUT.relative_to(ROOT).as_posix()
    except ValueError:
        out_label = OUT.as_posix()
    print(
        f"wrote {out_label} ({OUT.stat().st_size:,} bytes, "
        f"Palomar-archive appendix, {n_listings} listings, "
        f"{n_figures} mermaid figures, {note})"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
