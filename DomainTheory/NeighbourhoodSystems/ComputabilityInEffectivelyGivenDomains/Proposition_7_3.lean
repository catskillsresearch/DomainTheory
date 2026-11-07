module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.computableCategory

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems
open NeighborhoodSystem ApproximableMap

/-- Scott's Proposition 7.3: identities and composition of computable maps are
computable, so the image of a computable element is computable, and principal
elements of a presentation are computable. -/
theorem proposition_73 {α β γ : Type*} {V : NeighborhoodSystem α} {W : NeighborhoodSystem β}
    {U : NeighborhoodSystem γ} (P : ComputablePresentation V) (Q : ComputablePresentation W)
    (R : ComputablePresentation U) :
    (∀ {f : ApproximableMap V W} {x : V.Element},
        ComputableMap P Q f → ComputableElement P x →
          ComputableElement Q (f.toElementMap x)) ∧
      (∀ {f : ApproximableMap V W} {g : ApproximableMap W U},
        ComputableMap P Q f → ComputableMap Q R g → ComputableMap P R (g.comp f)) ∧
        ComputableMap P P (idMap V) ∧
          (∀ n, ComputableElement P (V.principal (P.mem_X n))) :=
  ⟨fun hf hx => apply_isComputableElement hf hx,
    ⟨fun hf hg => comp_isComputable hf hg,
      ⟨idMap_isComputable P, fun n => principal_isComputableElement P n⟩⟩⟩

end DomainTheory.NeighbourhoodSystems
