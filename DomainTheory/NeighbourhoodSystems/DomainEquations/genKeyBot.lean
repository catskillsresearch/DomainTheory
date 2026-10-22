module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Definition63
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Theorem69
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62C
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516
public import DomainTheory.NeighbourhoodSystems.DomainEquations.StrictDomainObj
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Inst3
public import DomainTheory.NeighbourhoodSystems.DomainEquations.id_val
public import DomainTheory.NeighbourhoodSystems.DomainEquations.comp_val
public import DomainTheory.NeighbourhoodSystems.DomainEquations.tcObj_sys
public import DomainTheory.NeighbourhoodSystems.DomainEquations.sumMap3
public import DomainTheory.NeighbourhoodSystems.DomainEquations.isStrict_sumMap3
public import DomainTheory.NeighbourhoodSystems.DomainEquations.sinj0_mem_j0
public import DomainTheory.NeighbourhoodSystems.DomainEquations.sinj1_mem_j1
public import DomainTheory.NeighbourhoodSystems.DomainEquations.sinj2_mem_j2
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Tc_obj
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Tc_map_val
public import DomainTheory.NeighbourhoodSystems.DomainEquations.ccEquiv_apply
public import DomainTheory.NeighbourhoodSystems.DomainEquations.descMap_strBot
public import DomainTheory.NeighbourhoodSystems.DomainEquations.descMap_strElem
public import DomainTheory.NeighbourhoodSystems.DomainEquations.C_bot_eq_strBot_nil
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Tc

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise510


section Initial

open Example44 Example62C ExampleB Exercise419 Exercise516

variable (B : TAlgebra Tc)

/-- `T(g)` on `⊥` is `⊥`; precomposed with `k` it is `⊥` (both maps are strict). -/
theorem genKeyBot (g : ApproximableMap C B.carrier.sys) :
    B.str.1.toElementMap ((sumMap3 (h₀ := Example62C.unitSys_nonempty) (h₁ := Example62C.C_nonempty)
        (h₂ := Example62C.C_nonempty) (h₀' := Example62C.unitSys_nonempty) (h₁' := B.carrier.nonempty)
        (h₂' := B.carrier.nonempty) (idMap unitSys) g g).toElementMap (toCC (strBot [])))
      = B.carrier.sys.bot := by
  have hb : toCC (strBot []) = (sum3 unitSys C C Example62C.unitSys_nonempty Example62C.C_nonempty
      Example62C.C_nonempty).bot := by
    rw [← C_bot_eq_strBot_nil, ← Example62C.ccEquiv_apply]; exact ccEquiv.map_bot
  rw [hb, isStrict_iff_apply_bot.mp (isStrict_sumMap3 (h₀ := Example62C.unitSys_nonempty)
    (h₁ := Example62C.C_nonempty) (h₂ := Example62C.C_nonempty) (idMap unitSys) g g)]
  exact isStrict_iff_apply_bot.mp B.str.2

end Initial

end DomainTheory.NeighbourhoodSystems
