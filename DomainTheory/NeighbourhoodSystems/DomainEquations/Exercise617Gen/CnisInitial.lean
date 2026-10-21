/-ai
CnisInitial A records that the Tsig-algebra Cnalg A is initial. Its descent homomorphism is descAlgHom, and uniqueness of a homomorphism into any other Tsig-algebra is descAlgHom_uniq. That descent is the closed-form head recursion sending the empty string to the distinguished point of the target and sending a letter followed by a string to the corresponding successor operation, built without choice by liftCn, so the string system is the initial algebra of the functor sending X to the sum of a unit and a copy of X for each letter.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.mem_coneN
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.Cn_mem
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.Cn_master
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
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.sumMapSig_rel
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.tsigObj_sys
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.tsigMapHom_val
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.Tsig_obj
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.Tsig_map_val
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.mem_embA
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.toCC_mem_jU
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.toCC_mem_jc
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.fromCC_mem_nil
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.fromCC_mem_embA
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.ccEquiv_apply
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.Cnobj_sys
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.Cnalg
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.descMap_strBot
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.descMap_strElem
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.descAlgHom
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.descAlgHom_uniq

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise617Gen

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise510

variable {A : Type} [DecidableEq A]

/-- **Exercise 6.17 part 2 — `(Cₐ, i)` is an initial `Tsig`-algebra for `Tsig(X) = 𝟙 + Σ_a X`.**
The descent map `φ : Cₐ → E` is the closed-form head-recursion `φ(Λ) = e`, `φ(a·x) = f_a(φ x)`
(`f_a = k ∘ inj_a`), built choice-free via `liftCn`; it is the unique `Tsig`-algebra homomorphism, so
`Cₐ` is the initial algebra of `X ↦ 𝟙 + Σ_a X`. -/
def CnisInitial (A : Type) [DecidableEq A] [Inhabited A] : IsInitial (Cnalg A) where
  desc := descAlgHom
  uniq := fun B h => descAlgHom_uniq B h

end DomainTheory.NeighbourhoodSystems.Exercise617Gen
