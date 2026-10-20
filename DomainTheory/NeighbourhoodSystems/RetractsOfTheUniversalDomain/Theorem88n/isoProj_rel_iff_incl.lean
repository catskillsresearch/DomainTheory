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





/-- **`isoProj`'s relation at raw indices reduces to a single reindexed inclusion.** `m := eIdx P a`
is always a valid witness (`e P (eIdx P a) = P.X a` by involutivity), and any *other* witness `m`
with `P.X a = e P m` forces `Yc P (eIdx P a) = Yc P m` (via `embed_eq_iff_raw_code` and
`eIdx_involutive`), so it gives no new information. -/
theorem isoProj_rel_iff_incl {b a : ℕ} :
    (isoProj P).rel (Yc P b) (P.X a) ↔ Yc P b ⊆ Yc P (eIdx P a) := by
  show (∃ _ : (DprimeUCode P).mem (Yc P b),
      (toDCode P ((DprimeUCode P).principal ⟨b, rfl⟩)).mem (P.X a)) ↔ _
  simp only [toDCode]
  have hea : e P (eIdx P a) = P.X a := by
    show P.X (eIdx P (eIdx P a)) = P.X a
    rw [eIdx_involutive P a]
  constructor
  · rintro ⟨-, m, hm, -, hsub⟩
    have heq : e P (eIdx P a) = e P m := hea.trans hm
    rw [(embed_eq_iff_raw_code P (eIdx P a) m).mp heq]
    exact hsub
  · intro hsub
    exact ⟨⟨b, rfl⟩, eIdx P a, hea.symm, ⟨eIdx P a, rfl⟩, hsub⟩

end DomainTheory.NeighbourhoodSystems
