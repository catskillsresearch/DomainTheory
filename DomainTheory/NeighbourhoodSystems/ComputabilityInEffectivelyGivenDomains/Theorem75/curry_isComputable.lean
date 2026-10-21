/-ai
If a map out of a product is computable, its currying into the function space is computable.

Reindex the recursively enumerable relation of the map so that it relates the product of the domain neighbourhood with the input half of an entry to the output half. The bounded universal of that relation over the decoded list is recursively enumerable, as is failure of the consistency character. Their disjunction matches the currying relation, which is the implication from consistency of the code to that universal.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition72
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem74
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75.Basic
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75.curry_rel_Xenum_iff

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap

variable {α β γ : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}










variable (P₀ : ComputablePresentation V₀) (P₁ : ComputablePresentation V₁)










































































































/-- **Theorem 7.5 (Scott 1981, PRG-19) — `curry` is computable (choice-free).** If `g : 𝒟₀ × 𝒟₁ → 𝒟₂`
is computable then so is `curry g : 𝒟₀ → (𝒟₁ → 𝒟₂)`: its neighbourhood relation is the parameterised
bounded `∀` (`REPred.forall_mem_decodeList₂`) over the r.e. relation of `g`, guarded by the decidable
consistency flag. -/
theorem curry_isComputable {V₂ : NeighborhoodSystem γ} (P₂ : ComputablePresentation V₂)
    (gN incl0 incl1 eq1 : ℕ → ℕ)
    (hgN : ∀ c, gN c = 1 ↔ (stepFun (funListOf P₁ P₂ (decodeList c))
      : Set (ApproximableMap V₁ V₂)).Nonempty) (hgNp : Nat.Primrec gN)
    (hincl0 : ∀ s, incl0 s = 1 ↔ P₁.X s.unpair.1 ⊆ P₁.X s.unpair.2) (hincl0p : Nat.Primrec incl0)
    (hincl1 : ∀ s, incl1 s = 1 ↔ P₂.X s.unpair.1 ⊆ P₂.X s.unpair.2) (hincl1p : Nat.Primrec incl1)
    (heq1 : ∀ s, eq1 s = 1 ↔ P₂.X s.unpair.1 = P₂.X s.unpair.2) (heq1p : Nat.Primrec eq1)
    {g : ApproximableMap (prod V₀ V₁) V₂}
    (hg : IsComputableMap (prodPresentation P₀ P₁) P₂ g) :
    IsComputableMap P₀ (funPresentation P₁ P₂ gN incl0 incl1 eq1 hgN hgNp hincl0 hincl0p
      hincl1 hincl1p heq1 heq1p) (curry g) := by
  have hg' : REPred (fun s => g.rel ((prodPresentation P₀ P₁).X s.unpair.1) (P₂.X s.unpair.2)) := hg
  have hre : Nat.Primrec (fun s => Nat.pair (Nat.pair s.unpair.1 s.unpair.2.unpair.1)
      s.unpair.2.unpair.2) :=
    (Nat.Primrec.left.pair (Nat.Primrec.left.comp Nat.Primrec.right)).pair
      (Nat.Primrec.right.comp Nat.Primrec.right)
  -- `g`'s relation re-indexed to `(n, e) ↦ X₀ₙ ∪ X₁_{e.1} g X₂_{e.2}` is r.e. in `(n, e)`.
  have hS : REPred₂ (fun n e =>
      g.rel (prodNbhd (P₀.X n) (P₁.X e.unpair.1)) (P₂.X e.unpair.2)) := by
    refine REPred.of_iff (fun s => ?_) (hg'.comp hre)
    simp only [prodPresentation_X, unpair_pair_fst, unpair_pair_snd]
  -- bounded `∀` over the coded list, with parameter `n = t.1`
  have hforall : REPred (fun t => ∀ e ∈ decodeList t.unpair.2,
      g.rel (prodNbhd (P₀.X t.unpair.1) (P₁.X e.unpair.1)) (P₂.X e.unpair.2)) :=
    REPred.forall_mem_decodeList₂ hS
  have hne1 : REPred (fun t => ¬ gN t.unpair.2 = 1) :=
    ((RecDecidable.natEq (hgNp.comp Nat.Primrec.right) (Nat.Primrec.const 1)).not).re
  refine REPred.of_iff (fun t => ?_) (hne1.or hforall)
  show (curry g).rel (P₀.X t.unpair.1) (Xenum P₁ P₂ gN t.unpair.2) ↔ _
  rw [curry_rel_Xenum_iff P₀ P₁ P₂ gN hgN g t.unpair.1 t.unpair.2]
  exact Decidable.imp_iff_not_or

end DomainTheory.NeighbourhoodSystems
