/-ai
A chain of length n from the master neighbourhood under the approximable map of a function-space element factors through one neighbourhood of that element: the least map of the corresponding principal element realizes the same chain.

The argument is induction on the length. At zero the master neighbourhood of the function space belongs to the element and already carries the chain. At a successor the chain splits into an intermediate neighbourhood and a last step. The inductive hypothesis gives a neighbourhood of the element for the first part, the step set of the last step belongs to the element, and the filter is closed under intersection. The least map of that intersection lies above the least map of the first neighbourhood, because a contained set determines a larger principal and the function-space equivalence is monotone, so monotonicity of iteration keeps the intermediate neighbourhood. The step set belongs to the principal of the intersection, so that least map makes the last step, and the two relations are the successor chain.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.ApproximableExercises
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α : Type*} {V : NeighborhoodSystem α}


open ApproximableMap


/-- **Theorem 4.2 (Scott 1981, PRG-19) — Scott's equation (∗), hard half.** A finite `f`-chain
`Δ (toApproxMap φ)ⁿ X` factors through a *single* finite approximant `F ∈ φ`: there is a
neighbourhood `W ∈ φ` whose least map already realizes the same chain `Δ (↑W)ⁿ X`. The witness `W`
is accumulated as the intersection of the (finitely many) step-neighbourhoods used by the chain,
which lies in `φ` because `φ` is a filter. -/
theorem exists_principal_iterMap (V : NeighborhoodSystem α) (φ : (funSpace V V).Element) :
    ∀ (n : ℕ) (X : Set α), ((toApproxMap φ).iterMap n).rel V.master X →
      ∃ (W : Set (ApproximableMap V V)) (hw : φ.mem W),
        ((toApproxMap ((funSpace V V).principal (φ.sub hw))).iterMap n).rel V.master X := by
  intro n
  induction n with
  | zero =>
    intro X hX
    exact ⟨(funSpace V V).master, φ.master_mem, hX⟩
  | succ k ih =>
    intro X hX
    obtain ⟨Y, hY, hYX⟩ := hX
    obtain ⟨W₁, hw₁, hW₁⟩ := ih Y hY
    have hVY : V.mem Y := ((toApproxMap φ).iterMap k).rel_cod hY
    have hVX : V.mem X := (toApproxMap φ).rel_cod hYX
    have hw₂ : φ.mem (step Y X) := toApproxMap_rel.mp hYX
    have hwInter : φ.mem (W₁ ∩ step Y X) := φ.inter_mem hw₁ hw₂
    refine ⟨W₁ ∩ step Y X, hwInter, ?_⟩
    have hg₁g : toApproxMap ((funSpace V V).principal (φ.sub hw₁))
        ≤ toApproxMap ((funSpace V V).principal (φ.sub hwInter)) :=
      (funSpaceEquiv V V).monotone
        (((funSpace V V).principal_le_iff (φ.sub hw₁) (φ.sub hwInter)).mpr Set.inter_subset_left)
    have hYg : ((toApproxMap ((funSpace V V).principal (φ.sub hwInter))).iterMap k).rel V.master Y :=
      iterMap_mono_map hg₁g k V.master Y hW₁
    have hgYX : (toApproxMap ((funSpace V V).principal (φ.sub hwInter))).rel Y X := by
      show ((funSpace V V).principal (φ.sub hwInter)).mem (step Y X)
      exact ⟨step_mem hVY hVX, Set.inter_subset_right⟩
    exact ⟨Y, hYg, hgYX⟩

end DomainTheory.NeighbourhoodSystems
