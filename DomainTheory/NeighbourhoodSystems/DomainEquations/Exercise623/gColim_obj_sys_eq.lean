/-ai
The neighbourhood system of the image of the colimit under a rooted grammar expression equals the neighbourhood system of the colimit. Continuity on domains along the directed tower turns the image of the union of the levels into the union of the successor levels, which has the same neighbourhoods as the full union because the zero level is absorbed by the chain step. Both masters are the fixed-point token set.

The levels form a nonempty directed family of subsystems of the colimit, directed by passage to the maximum index, and colimit membership is membership in some level. Extensionality of neighbourhood systems reduces the claim to membership and masters. Continuity identifies a neighbourhood of the image with a neighbourhood of the image of some level, hence with a neighbourhood of the next level. Conversely, the chain step carries a neighbourhood of level n into the image of that level. The masters agree because the image of the zero level is the first level, the subsystem law equates its master with the master of the image of the colimit, and every level has master the fixed-point set, which is the master of the colimit.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise621
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Theorem69
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.gGen_master
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.gTower
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.gTower_zero
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.gTower_succ
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.gChain
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.gTower_master
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.gTower_le
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.gColim
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.mem_gColim
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.gColim_master
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.gTower_sub_colim
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.ext

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise619

open DomainTheory.NeighbourhoodSystems.Example62 DomainTheory.NeighbourhoodSystems.ExampleB DomainTheory.NeighbourhoodSystems.Exercise510

namespace Exercise619

/-- **`T(𝒟) = 𝒟` at the level of neighbourhood systems.** Membership: continuity on domains
(`obj_continuous`) along the directed tower turns `T(⋃ₙ Tⁿ({Γ}))` into `⋃ₙ Tⁿ⁺¹({Γ})`, which has the
same neighbourhoods as `⋃ₙ Tⁿ({Γ})` (the extra `n=0` level `T⁰({Γ})` is absorbed by the chain step).
Master: both are `Γ` (`gTower_master` through `obj_subsystem` of `Tⁿ({Γ}) ◁ 𝒟`). -/
theorem gColim_obj_sys_eq (T : GExpr) (hT : T.RootedConst) :
    (T.obj (gColim T hT)).sys = (gColim T hT).sys := by
  set ℱ : Set ScottSys := Set.range (gTower T) with hℱ
  have hne : ℱ.Nonempty := ⟨gTower T 0, 0, rfl⟩
  have hsub : ∀ D ∈ ℱ, D.sys ◁ (gColim T hT).sys := by
    rintro D ⟨n, rfl⟩; exact gTower_sub_colim T hT n
  have hdir : DirectedOn (fun a b => a.sys ◁ b.sys) ℱ := by
    rintro _ ⟨n, rfl⟩ _ ⟨m, rfl⟩
    exact ⟨gTower T (max n m), ⟨max n m, rfl⟩,
      gTower_le T hT (le_max_left n m), gTower_le T hT (le_max_right n m)⟩
  have hU : ∀ X, (gColim T hT).sys.mem X ↔ ∃ D ∈ ℱ, D.sys.mem X := by
    intro X; constructor
    · rintro ⟨n, hn⟩; exact ⟨gTower T n, ⟨n, rfl⟩, hn⟩
    · rintro ⟨D, ⟨n, rfl⟩, hn⟩; exact ⟨n, hn⟩
  apply NeighborhoodSystem.ext
  · intro W
    rw [T.obj_continuous hdir hne hsub hU W]
    constructor
    · rintro ⟨D, ⟨n, rfl⟩, hn⟩
      -- `T(Tⁿ({Γ})) = Tⁿ⁺¹({Γ})`, a level of the colimit.
      exact ⟨n + 1, hn⟩
    · rintro ⟨n, hn⟩
      -- a colimit neighbourhood at level `n` is, after one chain step, at `T(Tⁿ({Γ}))`.
      exact ⟨gTower T n, ⟨n, rfl⟩, (gChain T hT n).sub hn⟩
  · -- masters: `(T 𝒟).master = (Tⁿ⁺¹({Γ})).master = Γ = 𝒟.master`, via `obj_subsystem` at `n=0`.
    have h := (T.obj_subsystem (gTower_sub_colim T hT 0)).master_eq
    rw [gColim_master]
    rw [show (T.obj (gTower T 0)) = gTower T 1 from rfl] at h
    rw [← h, gTower_master T hT]

end Exercise619

end DomainTheory.NeighbourhoodSystems
