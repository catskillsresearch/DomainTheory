module
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Definition_3_1

public import Mathlib.Algebra.Group.End
public import Mathlib.Order.Hom.Basic
@[expose] public section

section
namespace DomainTheory.NeighbourhoodSystems
section
open NeighborhoodSystem
variable {α β γ δ : Type*}
variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

def prodEquiv (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β) :
    (prod V₀ V₁).Element ≃o V₀.Element × V₁.Element where
  toFun z := (z.fst, z.snd)
  invFun p := pair p.1 p.2
  left_inv z := pair_fst_snd z
  right_inv p := by simp
  map_rel_iff' := by
    intro z z'
    constructor
    · rintro ⟨h1, h2⟩ W hW
      obtain ⟨X, Y, hX, hY, rfl⟩ := z.sub hW
      obtain ⟨ha, hb⟩ := (prod_mem_split hX hY).mp hW
      have hX' : z'.fst.mem X := h1 X ⟨hX, ha⟩
      have hY' : z'.snd.mem Y := h2 Y ⟨hY, hb⟩
      exact (prod_mem_split hX hY).mpr ⟨hX'.2, hY'.2⟩
    · intro h
      exact ⟨fun X ⟨hX, hzX⟩ => ⟨hX, h _ hzX⟩, fun Y ⟨hY, hzY⟩ => ⟨hY, h _ hzY⟩⟩

@[simp] theorem prodEquiv_apply (z : (prod V₀ V₁).Element) :
    prodEquiv V₀ V₁ z = (z.fst, z.snd) := rfl

@[simp] theorem prodEquiv_symm_apply (p : V₀.Element × V₁.Element) :
    (prodEquiv V₀ V₁).symm p = pair p.1 p.2 := rfl

theorem pair_le_pair_iff {x x' : V₀.Element} {y y' : V₁.Element} :
    pair x y ≤ pair x' y' ↔ x ≤ x' ∧ y ≤ y' := by
  constructor
  · intro h
    refine ⟨fun X hX => ?_, fun Y hY => ?_⟩
    · obtain ⟨X', Y', hX', hY', heq⟩ :=
        h (prodNbhd X V₁.master) ⟨X, V₁.master, hX, y.master_mem, rfl⟩
      obtain ⟨rfl, _⟩ := prodNbhd_injective heq
      exact hX'
    · obtain ⟨X', Y', hX', hY', heq⟩ :=
        h (prodNbhd V₀.master Y) ⟨V₀.master, Y, x.master_mem, hY, rfl⟩
      obtain ⟨_, rfl⟩ := prodNbhd_injective heq
      exact hY'
  · rintro ⟨hx, hy⟩ W ⟨X, Y, hX, hY, rfl⟩
    exact ⟨X, Y, hx X hX, hy Y hY, rfl⟩
end
end DomainTheory.NeighbourhoodSystems
end
