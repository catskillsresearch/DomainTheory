module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise122
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.sierpinski
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.mapOfOpen
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.mapOfOpen_rel
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.mapOfOpen_rel_empty
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.openOfMap
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.openOfMap_isOpen

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems.Exercise325

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem Set

variable {α : Type*} (V : NeighborhoodSystem α)

/-- **Exercise 3.25 (core).** The open subsets of `|𝒟|` (ordered by `⊆`) are order-isomorphic to the
approximable maps `𝒟 → 𝒪`. -/
def openIso (V : NeighborhoodSystem α) :
    {U : Set V.Element // IsOpen U} ≃o ApproximableMap V sierpinski where
  toFun U := mapOfOpen V U.1
  invFun f := ⟨openOfMap V f, openOfMap_isOpen V f⟩
  left_inv U := by
    apply Subtype.ext
    ext x
    constructor
    · rintro ⟨X, hxX, hrel⟩
      rw [mapOfOpen_rel_empty] at hrel
      exact hrel.2 hxX
    · intro hx
      obtain ⟨X, hxX, hsub⟩ := U.2 x hx
      exact ⟨X, hxX, (mapOfOpen_rel_empty V U.1 X).mpr ⟨x.sub hxX, hsub⟩⟩
  right_inv f := by
    apply ApproximableMap.ext
    intro X Y
    rw [mapOfOpen_rel]
    constructor
    · rintro ⟨hX, hd⟩
      rcases hd with rfl | ⟨rfl, hsub⟩
      · exact f.mono f.master_rel (V.sub_master hX) (Set.subset_univ _) hX (Or.inl rfl)
      · have hpr : V.principal hX ∈ V.basicOpen X := ⟨hX, subset_rfl⟩
        obtain ⟨X', hX', hf⟩ := hsub hpr
        exact f.mono hf hX'.2 subset_rfl hX (Or.inr rfl)
    · intro hf
      refine ⟨f.rel_dom hf, ?_⟩
      rcases f.rel_cod hf with rfl | rfl
      · left; rfl
      · exact Or.inr ⟨rfl, fun z hz => ⟨X, hz, hf⟩⟩
  map_rel_iff' := by
    intro a b
    show mapOfOpen V a.1 ≤ mapOfOpen V b.1 ↔ a ≤ b
    rw [ApproximableMap.le_iff]
    constructor
    · intro h x hx
      obtain ⟨X, hxX, hsub⟩ := a.2 x hx
      have hrelB := h X ∅ ((mapOfOpen_rel_empty V a.1 X).mpr ⟨x.sub hxX, hsub⟩)
      rw [mapOfOpen_rel_empty] at hrelB
      exact hrelB.2 hxX
    · intro h X Y hrel
      rw [mapOfOpen_rel] at hrel ⊢
      obtain ⟨hX, hd⟩ := hrel
      refine ⟨hX, ?_⟩
      rcases hd with hu | ⟨he, hsub⟩
      · exact Or.inl hu
      · exact Or.inr ⟨he, fun z hz => h (hsub hz)⟩

end DomainTheory.NeighbourhoodSystems.Exercise325
