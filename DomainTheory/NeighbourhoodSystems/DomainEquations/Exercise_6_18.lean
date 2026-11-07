module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.iterProdInitial

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Theorem_6_14

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.SmashProduct

namespace Exercise618

def iterIsInitial (Dom : StrictDomainObj.{w}) : IsInitial (iterAlg Dom) where
  desc := descAlgHom Dom
  uniq B h := by
    obtain ⟨hom, comm⟩ := h
    have hcomm : hom.1.comp (imap Dom.sys)
        = B.str.1.comp (prodMap (idMap Dom.sys) hom.1) := congrArg Subtype.val comm
    have hg : hom.1 = descMap B.str.1 :=
      comm_unique B.str.1 hom.2 (descMap_strict B.str.1 B.str.2) hcomm (descMap_comm B.str.1)
    have hhom : hom = ⟨descMap B.str.1, descMap_strict B.str.1 B.str.2⟩ := Subtype.ext hg
    subst hhom
    rfl

end Exercise618

/-- Scott's Exercise 6.18: strictness is preserved by the product of two approximable maps. -/
theorem example_618 {α β α' β' : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
    {V₀' : NeighborhoodSystem α'} {V₁' : NeighborhoodSystem β'} {f₀ : ApproximableMap V₀ V₀'}
    {f₁ : ApproximableMap V₁ V₁'} :
    IsStrict f₀ → IsStrict f₁ → IsStrict (prodMap f₀ f₁) :=
  Exercise618.isStrict_prodMap

end DomainTheory.NeighbourhoodSystems
