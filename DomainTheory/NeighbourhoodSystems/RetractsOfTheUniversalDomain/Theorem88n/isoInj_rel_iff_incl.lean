/-ai
The code-level injection relates the neighbourhood at a raw index to the coded neighbourhood at another index if and only if the first neighbourhood is contained in the neighbourhood at the involute of the second index.

The relation is membership of the first neighbourhood together with membership of the coded neighbourhood in the image of its principal filter under the coding map into the copy. Simplify membership in a principal filter. The embedding of the second index is the neighbourhood at its involute. In the forward direction a witness index with the same coded neighbourhood rewrites, by the agreement of embeddings with equality of coded neighbourhoods, to the inclusion in that involute neighbourhood. In the reverse direction the second index itself is a witness, using membership of the presented neighbourhood and of the coded neighbourhood, and the identification of the embedding.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88f.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88f.DprimeUCode_inj_isComputableMap
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88f.DprimeUCode_proj_isComputableMap
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88f.DprimeUCode_projectionPair_isComputable
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88n.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap

variable {α : Type*} {D : NeighborhoodSystem α} (P : ComputablePresentation D)


/-- **`isoInj`'s relation at raw indices reduces to a single reindexed inclusion.** `n := b` is always
a valid witness (`Yc P b = Yc P b`), and any *other* witness `n` with `Yc P b = Yc P n` forces
`e P b = e P n` (`embed_eq_iff_raw_code`), so it gives no new information. -/
theorem isoInj_rel_iff_incl {a b : ℕ} :
    (isoInj P).rel (P.X a) (Yc P b) ↔ P.X a ⊆ P.X (eIdx P b) := by
  show (∃ _ : D.mem (P.X a), (toDprimeUCode P (D.principal (P.mem_X a))).mem (Yc P b)) ↔ _
  simp only [toDprimeUCode, mem_principal]
  have hb : e P b = P.X (eIdx P b) := rfl
  constructor
  · rintro ⟨-, n, hn, -, hsub⟩
    rwa [← hb, (embed_eq_iff_raw_code P b n).mpr hn]
  · intro hsub
    exact ⟨P.mem_X a, b, rfl, (P0 P).mem_X b, hb ▸ hsub⟩

end DomainTheory.NeighbourhoodSystems
