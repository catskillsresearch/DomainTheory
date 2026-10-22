module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition83
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84b.prod_bot_fst
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84b.prod_bot_snd
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84b.toFilter_toApproxMap
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84b.toApproxMap_toFilter
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84b.strictRetraction
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84b.strictRetraction_apply_bot
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84b.strictRetraction_apply_of_ne_bot

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap ApproximableMap₂

variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}

section Strict

theorem strictRetraction_fixed_of_isStrict {f : ApproximableMap D E} (hf : Exercise510.IsStrict f) :
    strictRetraction.toElementMap (toFilter f) = toFilter f := by
  have hbot : f.toElementMap D.bot = E.bot := Exercise510.isStrict_iff_apply_bot.mp hf
  have key : toApproxMap (strictRetraction.toElementMap (toFilter f)) = f := by
    apply ext_of_toElementMap
    intro y
    by_cases hy : y = D.bot
    · rw [hy, strictRetraction_apply_bot, hbot]
    · rw [strictRetraction_apply_of_ne_bot hy, toApproxMap_toFilter]
  rw [← toFilter_toApproxMap (strictRetraction.toElementMap (toFilter f)), key]

end Strict

end DomainTheory.NeighbourhoodSystems
