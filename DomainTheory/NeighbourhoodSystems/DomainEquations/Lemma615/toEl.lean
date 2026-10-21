/-ai
toEl sends an element of the domain system to the element of the image subdomain whose members are the generators of members of that element.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Definition610
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Lemma615.IsGen
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Lemma615.isGen_master
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Lemma615.isGen_mono
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Lemma615.isGen_inter
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Lemma615.Dprime
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Lemma615.mem_Dprime
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Lemma615.Basic.notation4

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}

section ProjectionPair

variable (i : ApproximableMap D E) (j : ApproximableMap E D)

/-- **Forward map of the isomorphism `D ≅ D'`.** `x ↦ {Y ∣ ∃ X ∈ x, IsGen i j X Y}` — the
generators of the members of `x`. (Needs `j ∘ i = I_D` for upward closure, via `isGen_mono`.) -/
def toEl (hji : j.comp i = idMap D) (x : D.Element) : (Dprime i j).Element where
  mem Y := ∃ X, x.mem X ∧ IsGen i j X Y
  sub := by rintro Y ⟨X, _, hg⟩; exact ⟨X, hg⟩
  master_mem := ⟨D.master, x.master_mem, isGen_master i j⟩
  inter_mem := by
    rintro Y₁ Y₂ ⟨X₁, hX₁x, hg₁⟩ ⟨X₂, hX₂x, hg₂⟩
    have hxInter : x.mem (X₁ ∩ X₂) := x.inter_mem hX₁x hX₂x
    have hDInter : D.mem (X₁ ∩ X₂) := x.sub hxInter
    have hi1 : i.rel (X₁ ∩ X₂) Y₁ :=
      i.mono hg₁.1 Set.inter_subset_left subset_rfl hDInter (i.rel_cod hg₁.1)
    have hi2 : i.rel (X₁ ∩ X₂) Y₂ :=
      i.mono hg₂.1 Set.inter_subset_right subset_rfl hDInter (i.rel_cod hg₂.1)
    have hEinter : E.mem (Y₁ ∩ Y₂) := i.rel_cod (i.inter_right hi1 hi2)
    exact ⟨X₁ ∩ X₂, hxInter, isGen_inter i j hg₁ hg₂ hEinter⟩
  up_mem := by
    rintro Y Y' ⟨X, hXx, hg⟩ ⟨X', hg'⟩ hYY'
    have hXX' : X ⊆ X' := isGen_mono i j hji hg hg' hYY'
    exact ⟨X', x.up_mem hXx (i.rel_dom hg'.1) hXX', hg'⟩

end ProjectionPair

end DomainTheory.NeighbourhoodSystems
