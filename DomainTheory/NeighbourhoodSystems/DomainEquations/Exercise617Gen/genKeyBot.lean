/-ai
Applying the structure map of a Tsig-algebra to the sum map of an approximable map, at the image under toCC of the partial element named by the empty string, yields the bottom element of the carrier.

That partial element is the bottom element of the string system, so its image under the isomorphism is the bottom element of the sum system. The sum map is strict, so it sends that bottom element to the bottom element of the sum, and the structure map is strict, so it sends that bottom element to the bottom element of the carrier.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.Strn
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.mem_coneN
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.Cn
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.Cn_mem
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.Cn_master
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.Cn_nonempty
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.strBotN
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.mem_prependN
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.consMapN_rel
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.tc_mem_jc
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.mem_jU
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.none_not_mem_jU
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.none_not_mem_jc
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.tu_not_mem_jc
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.tc_not_mem_jU
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.none_mem_masterSig
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.tu_mem_masterSig
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.sumSig_master
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.sinjU_mem_jU
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.sinjC_mem_jc
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.sumMapSig
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.isStrict_sumMapSig
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.sumMapSig_rel
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.tsigObj_sys
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.tsigMapHom_val
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.Tsig_obj
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.Tsig_map_val
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.mem_embA
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.CCn
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.toCC
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.toCC_mem_jU
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.toCC_mem_jc
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.fromCC_mem_nil
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.fromCC_mem_embA
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.ccEquiv
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.ccEquiv_apply
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.Cnobj_sys
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.descMap_strBot
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.descMap_strElem
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.Cn_bot_eq_strBotN_nil
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.Tsig

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise617Gen

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise510

variable {A : Type} [DecidableEq A]

section Initial

variable {A : Type} [DecidableEq A] [Inhabited A] (B : TAlgebra (Tsig A))

theorem genKeyBot (g : ApproximableMap (Cn A) B.carrier.sys) :
    B.str.1.toElementMap ((sumMapSig (A := A) (h₀ := Cn_nonempty) (h₁ := B.carrier.nonempty)
        g).toElementMap (toCC (strBotN ([] : Strn A))))
      = B.carrier.sys.bot := by
  have hb : toCC (strBotN ([] : Strn A)) = (CCn A).bot := by
    rw [← Cn_bot_eq_strBotN_nil, ← ccEquiv_apply]; exact ccEquiv.map_bot
  rw [hb, isStrict_iff_apply_bot.mp (isStrict_sumMapSig (A := A) (h₀ := Cn_nonempty)
    (h₁ := B.carrier.nonempty) g)]
  exact isStrict_iff_apply_bot.mp B.str.2

end Initial

end DomainTheory.NeighbourhoodSystems.Exercise617Gen
