module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Approximable
public import Mathlib.Data.Set.Image
import all Mathlib.Data.Set.Image
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.ApproximableExercises.ApproximableMap₂

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α β γ : Type*}

namespace ApproximableMap₂

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}

/-- **Exercise 2.19 (Proposition 2.2 analogue).** A two-variable approximable mapping determines an
elementwise function of two arguments: `f(x, y) = {Z ∣ ∃ X ∈ x, ∃ Y ∈ y, X, Y f Z}`. The filter
laws use all three conditions: `inter_mem` pulls both outputs back to `(X ∩ X', Y ∩ Y')` via `mono`
then `inter_right`. -/
def toElementMap₂ (f : ApproximableMap₂ V₀ V₁ V₂) (x : V₀.Element) (y : V₁.Element) : V₂.Element where
  mem Z := ∃ X Y, x.mem X ∧ y.mem Y ∧ f.rel X Y Z
  sub := fun ⟨_, _, _, _, hrel⟩ => f.rel_cod hrel
  master_mem := ⟨V₀.master, V₁.master, x.master_mem, y.master_mem, f.master_rel⟩
  inter_mem := by
    rintro Z Z' ⟨X, Y, hX, hY, hrel⟩ ⟨X', Y', hX', hY', hrel'⟩
    have hXX' : x.mem (X ∩ X') := x.inter_mem hX hX'
    have hYY' : y.mem (Y ∩ Y') := y.inter_mem hY hY'
    have hXX'm : V₀.mem (X ∩ X') := x.sub hXX'
    have hYY'm : V₁.mem (Y ∩ Y') := y.sub hYY'
    refine ⟨X ∩ X', Y ∩ Y', hXX', hYY', ?_⟩
    have h1 : f.rel (X ∩ X') (Y ∩ Y') Z :=
      f.mono hrel Set.inter_subset_left Set.inter_subset_left subset_rfl hXX'm hYY'm (f.rel_cod hrel)
    have h2 : f.rel (X ∩ X') (Y ∩ Y') Z' :=
      f.mono hrel' Set.inter_subset_right Set.inter_subset_right subset_rfl hXX'm hYY'm
        (f.rel_cod hrel')
    exact f.inter_right h1 h2
  up_mem := by
    rintro Z Z' ⟨X, Y, hX, hY, hrel⟩ hZ' hZZ'
    exact ⟨X, Y, hX, hY, f.mono hrel subset_rfl subset_rfl hZZ' (x.sub hX) (y.sub hY) hZ'⟩

end ApproximableMap₂

end DomainTheory.NeighbourhoodSystems
