module

public import DomainTheory.ContinuousLattice.MilnerCorrection
public import DomainTheory.ContinuousLattice.ScottMaps
public import DomainTheory.ContinuousLattice.Injective
public import Mathlib.Order.Preorder.Finite
import all Mathlib.Order.Preorder.Finite
public import DomainTheory.ContinuousLattice.Constructions.Basic

@[expose] public section


namespace DomainTheory.ContinuousLattice

open Topology Set

variable {D : Type*} [CompleteLattice D]

/-- **Scott 1972, Proposition 2.9(a) (order-theoretic content).** The Cartesian product of any
family of continuous lattices is a continuous lattice. (Part (b), that the induced topology of
the product agrees with the product topology, is `proposition_2_9_b` below; `proposition_2_9`
bundles the two.)

The key step is that if `a ≪ yᵢ` in the factor `Dᵢ`, then the cylinder element `[a]ⁱ`
(equal to `a` in coordinate `i` and `⊥` elsewhere) is way below `y` in the product: the
preimage `{z | zᵢ ∈ U}` of a Scott-open witness `U ⊆ Dᵢ` is Scott-open in the product
(suprema are computed coordinatewise). Any upper bound `b` of `{x | x ≪ y}` therefore
dominates every `[a]ⁱ`, so `a = ([a]ⁱ)ᵢ ≤ bᵢ`; ranging over `a ≪ yᵢ` and using continuity of
`Dᵢ` gives `yᵢ ≤ bᵢ` for all `i`, i.e. `y ≤ b`. -/
theorem proposition_2_9_a {ι : Type*} (E : ι → Type*) [∀ i, CompleteLattice (E i)]
    (hE : ∀ i, IsContinuousLattice (E i)) : IsContinuousLattice (∀ i, E i) := by
  classical
  intro y
  refine ⟨fun x hx => hx.le, fun b hb => ?_⟩
  rw [Pi.le_def]
  intro i
  rw [← (hE i).sSup_wayBelow (y i)]
  apply sSup_le
  intro a ha
  set e : (∀ j, E j) := Function.update (⊥ : ∀ j, E j) i a with he
  have hei : e i = a := by rw [he]; exact Function.update_self i a _
  have hcyl : e ≪ y := by
    obtain ⟨U, hU, hyiU, hUsub⟩ := ha
    refine ⟨{z : ∀ j, E j | z i ∈ U}, ?_, hyiU, ?_⟩
    · refine ⟨fun z w hzw hz => hU.1 (hzw i) hz, fun S hSne hSdir hmem => ?_⟩
      rw [Set.mem_ofPred_eq, sSup_apply_eq_sSup_image] at hmem
      have hdir' : DirectedOn (· ≤ ·) (Function.eval i '' S) := by
        rintro _ ⟨f, hf, rfl⟩ _ ⟨g, hg, rfl⟩
        obtain ⟨h, hhS, hfh, hgh⟩ := hSdir f hf g hg
        exact ⟨Function.eval i h, ⟨h, hhS, rfl⟩, hfh i, hgh i⟩
      obtain ⟨t, htimg, htU⟩ := hU.2 (hSne.image _) hdir' hmem
      obtain ⟨f, hfS, rfl⟩ := htimg
      exact ⟨f, hfS, htU⟩
    · intro z hz
      rw [Set.mem_Ici, Pi.le_def]
      intro j
      rcases eq_or_ne j i with rfl | hji
      · rw [hei]; exact Set.mem_Ici.1 (hUsub hz)
      · rw [he, Function.update_of_ne hji]; exact bot_le
  have hle : e i ≤ b i := (hb hcyl) i
  rw [hei] at hle
  exact hle

end DomainTheory.ContinuousLattice
