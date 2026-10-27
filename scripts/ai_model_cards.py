"""Model-card registry for the AI-assisted development acknowledgements block.

Injected into `arxiv.md` / `arxiv.tex` by `build_arxiv_tex.py` at:
  <!-- AI_MODEL_TOOL_BULLETS --> … <!-- /AI_MODEL_TOOL_BULLETS -->

This revision acknowledges three models only. Source packages under `vendor/`
keep the model cards in their own writeups.
"""

from __future__ import annotations

import re
from dataclasses import dataclass


@dataclass(frozen=True)
class ModelCard:
    label: str
    cite_key: str
    tool_note: str
    # BibTeX fields for references.bib (same format as the rest of the bibliography).
    bib_entry_type: str
    bib_fields: dict[str, str]


MODEL_CARDS: tuple[ModelCard, ...] = (
    ModelCard(
        label="Cursor Composer 2.5",
        cite_key="Cmp25",
        tool_note=(
            "routine multi-step work: module scaffolding, dependency-ordered wiring of "
            "`DomainTheory/`, documentation and Mermaid blueprints, and medium proof "
            "obligations where the strategy was already fixed (`composer-2.5`)."
        ),
        bib_entry_type="misc",
        bib_fields={
            "author": "{Anysphere, Inc.}",
            "title": "Composer 2.5",
            "howpublished":
                "Model announcement and documentation, "
                "\\url{https://cursor.com/blog/composer-2-5}; "
                "model card as integrated in Cursor, "
                "\\url{https://cursor.com/docs/models}",
            "year": "2026",
            "note": "accessed 2026",
        },
    ),
    ModelCard(
        label="Cursor Grok 4.7",
        cite_key="Grk47",
        tool_note=(
            "primary agent model for the DomainTheory sessions: domain-theory "
            "constructions, inventory design in `arxiv.md`, constructivity audits, "
            "and adaptation of portable patterns from prior Scott formalizations. "
            "Used here via the Cursor agent environment."
        ),
        bib_entry_type="misc",
        bib_fields={
            "author": "xAI and {Anysphere, Inc.}",
            "title": "Grok 4.7",
            "howpublished":
                "Model documentation, \\url{https://docs.x.ai/docs/models}; "
                "Cursor model catalog, \\url{https://cursor.com/docs/models}",
            "year": "2026",
            "note": "accessed 2026",
        },
    ),
    ModelCard(
        label="Google Gemini 3.8",
        cite_key="Gem38",
        tool_note=(
            "exploratory and support passes (typographic conventions, scope decisions, "
            "and cross-checks against the narrative inventory)."
        ),
        bib_entry_type="misc",
        bib_fields={
            "author": "{Google DeepMind}",
            "title": "Gemini 3.8",
            "howpublished":
                "Technical documentation and model cards, "
                "\\url{https://ai.google.dev/gemini-api/docs/models}",
            "year": "2026",
            "note": "accessed 2026",
        },
    ),
)

TOOL_BULLETS_BEGIN = "<!-- AI_MODEL_TOOL_BULLETS -->"
TOOL_BULLETS_END = "<!-- /AI_MODEL_TOOL_BULLETS -->"
REFERENCES_BEGIN = "<!-- AI_MODEL_REFERENCES -->"
REFERENCES_END = "<!-- /AI_MODEL_REFERENCES -->"

# Acknowledgments live outside `arxiv.md` and are spliced in when building `arxiv.tex`.
ACKNOWLEDGMENTS_MARKDOWN = r"""## Acknowledgments

### AI-assisted development

The human author retains sole responsibility for the mathematical content, the choice of
formalization route, and every formal claim in this work. Following standard publisher practice
(e.g., COPE guidance on authorship and AI tools \cite{COPE24}), **no large language model is listed
as a co-author** — authorship implies an accountability that automated systems cannot bear.

We gratefully acknowledge assistance from the following tools in this revision
(auto-generated from `scripts/ai_model_cards.py` when building `arxiv.tex`). Source versions of
the four Scott papers and the bridge theorems record their own model cards in their respective
writeups under `vendor/`:

<!-- AI_MODEL_TOOL_BULLETS -->
<!-- /AI_MODEL_TOOL_BULLETS -->

All definitions, constructivity audits, and final prose were reviewed by the human author, who takes
full responsibility for them.

### Artifact availability and reproducibility

The development is at
[`github.com/catskillsresearch/DomainTheory`](https://github.com/catskillsresearch/DomainTheory).
GitHub Actions CI runs `lake build` on `main`.

Locally:

```bash
lake exe cache get
lake build DomainTheory
```

Sibling packages `scott1972`, `scott1976`, `scott1980`, `scott1982`, and `scott_models`
are vendored under `vendor/` (frozen revisions in `vendor/FROZEN.txt`); they are not
Lake path dependencies. `arxiv.md` is the durable inventory
and proof narrative. Axiom audits: `#print axioms` on the compared names in
`comparator.json`.

Build the arXiv PDF / submission zip (Lean Code appendix = GitHub hyperlinks):

```bash
bash scripts/build_arxiv_tex.sh      # arxiv.md → arxiv.tex + figures/
bash scripts/build_arxiv_pdf.sh      # compile PDF + package dist/arxiv_submit.zip
# or: bash scripts/package_arxiv_submit.sh
```

"""


def render_tool_bullets() -> str:
    return "\n".join(
        f"- **{card.label}** \\cite{{{card.cite_key}}} — {card.tool_note}"
        for card in MODEL_CARDS
    )


def render_model_bibtex() -> str:
    """BibTeX entries for the three model cards (same shape as references.bib)."""
    blocks: list[str] = []
    for card in MODEL_CARDS:
        lines = [f"@{card.bib_entry_type}{{{card.cite_key},"]
        for key, value in card.bib_fields.items():
            lines.append(f"  {key} = {{{value}}},")
        lines.append("}")
        blocks.append("\n".join(lines))
    return "\n\n".join(blocks)


def inject_acknowledgments(text: str) -> str:
    """Insert the Acknowledgments section before References (skipped if already present)."""
    if re.search(r"^##\s+Acknowledgments\s*$", text, re.MULTILINE):
        return text
    m = re.search(r"^##\s+References\s*$", text, re.MULTILINE)
    if not m:
        raise RuntimeError(
            "missing ## References in narrative; needed to place Acknowledgments before it"
        )
    return text[: m.start()] + ACKNOWLEDGMENTS_MARKDOWN + "\n" + text[m.start() :]


def inject_model_cards(text: str) -> str:
    """Insert Acknowledgments (if needed), then expand AI model-card tool bullets.

    Model-card bibliographic entries live in ``references.bib``; the old
    ``AI_MODEL_REFERENCES`` marker block is cleared if present.
    """
    text = inject_acknowledgments(text)
    if TOOL_BULLETS_BEGIN not in text:
        raise RuntimeError(
            f"missing {TOOL_BULLETS_BEGIN} after Acknowledgments injection"
        )

    text = _replace_between(text, TOOL_BULLETS_BEGIN, TOOL_BULLETS_END, render_tool_bullets())
    if REFERENCES_BEGIN in text and REFERENCES_END in text:
        text = _replace_between(text, REFERENCES_BEGIN, REFERENCES_END, "")
    return text


def _replace_between(text: str, begin: str, end: str, body: str) -> str:
    start = text.index(begin)
    stop = text.index(end, start)
    stop_end = stop + len(end)
    inner_start = start + len(begin)
    # Preserve one leading newline after begin marker when present.
    if inner_start < stop and text[inner_start : inner_start + 1] == "\n":
        inner_start += 1
    if inner_start < stop and text[stop - 1 : stop] == "\n":
        stop -= 1
    if body:
        return text[:start] + begin + "\n" + body + "\n" + end + text[stop_end:]
    return text[:start] + begin + "\n" + end + text[stop_end:]
