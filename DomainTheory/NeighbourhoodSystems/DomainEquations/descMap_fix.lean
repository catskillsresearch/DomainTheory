module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise319
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617
public import DomainTheory.NeighbourhoodSystems.DomainEquations.consSeq_zero
public import DomainTheory.NeighbourhoodSystems.DomainEquations.consSeq_succ
public import DomainTheory.NeighbourhoodSystems.DomainEquations.component_bot
public import DomainTheory.NeighbourhoodSystems.DomainEquations.descOp
public import DomainTheory.NeighbourhoodSystems.DomainEquations.descOp_apply
public import DomainTheory.NeighbourhoodSystems.DomainEquations.descSeq
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise618.descMap
public import DomainTheory.NeighbourhoodSystems.DomainEquations.descSeqEltMono
public import DomainTheory.NeighbourhoodSystems.DomainEquations.descMap_eq
public import DomainTheory.NeighbourhoodSystems.DomainEquations.kHead
public import DomainTheory.NeighbourhoodSystems.DomainEquations.kHead_apply

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise510

universe w

namespace Exercise618

variable {α : Type*} {V : NeighborhoodSystem α}

section Target

variable {γ : Type*} {E : NeighborhoodSystem γ}

/-- **The descent map is a fixed point** of `Op = k ∘ T(·) ∘ j`. -/
theorem descMap_fix (k : ApproximableMap (prod V E) E) : descMap k = descOp k (descMap k) := by
  apply ext_of_toElementMap
  intro z
  rw [descOp_apply, descMap_eq k (ofSeq (fun n => component z (n + 1))),
    ← kHead_apply k (component z 0), toElementMap_iSupDirected, descMap_eq k z]
  -- both sides are directed unions; compare the (reindexed) families term-wise
  apply Element.ext
  intro Y
  rw [mem_iSupDirected, mem_iSupDirected]
  have hstep : ∀ m, (kHead k (component z 0)).toElementMap
        ((descSeq k m).toElementMap (ofSeq (fun n => component z (n + 1))))
      = (descSeq k (m + 1)).toElementMap z := by
    intro m
    rw [kHead_apply, show descSeq k (m + 1) = descOp k (descSeq k m) from rfl, descOp_apply]
  constructor
  · rintro ⟨n, hn⟩
    cases n with
    | zero => exact ⟨0, by rw [hstep 0]; exact descSeqEltMono k z 0 _ hn⟩
    | succ m => exact ⟨m, by rw [hstep m]; exact hn⟩
  · rintro ⟨m, hm⟩
    rw [hstep m] at hm
    exact ⟨m + 1, hm⟩

end Target

end Exercise618

end DomainTheory.NeighbourhoodSystems
