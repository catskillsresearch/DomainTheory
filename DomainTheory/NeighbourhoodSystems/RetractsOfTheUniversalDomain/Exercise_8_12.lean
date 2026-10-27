module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise_8_27
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise_7_18

@[expose] public section

/- concordance: source L5147 EXERCISE 8.12 integer presentation of U -/
namespace DomainTheory.NeighbourhoodSystems
open NeighborhoodSystem Exercise718

/-! ### Exercise 8.12 tips

Scott's paper statement is one sentence; the (a)–(e)/(f)/(g) labels were a formalization
scaffold. These tips assemble named library tools from `Exercise_8_12_more` / `Exercise_8_27`. -/

/-- **Exercise 8.12 (a)–(e) tip.** `V` is effectively given ((a)/(b)), and the U-as-prober
computable split `splitX812e` is an `IsComputableSplit` ((e), via «812e»). Abstract iso
headlines `isomorphic_812c` / `isomorphic_812d` / `effectivelyIsomorphic_812d` sit in
`Exercise_8_12_more` as reusable tools for the general `D₀`/`D₁` argument. -/
theorem exercise_8_12_ae :
    V.IsEffectivelyGiven ∧
      Nonempty (IsComputableSplit UComputablePresentation VComputablePresentation splitX812e) :=
  ⟨V_isEffectivelyGiven, ⟨isComputableSplit.«812e»⟩⟩

/-- **Exercise 8.12 (Scott 1981, PRG-19).** `V` is effectively given and effectively isomorphic
to `U`, hence another presentation of `U`.

Assembles the scaffold tips (a)–(g): `V` / `V_isEffectivelyGiven`, the abstract
`EffectiveIso` machinery of (c)/(d), and the concrete splits «812e» / «812f» via
`effectiveIso812_UV`. Library tools stay factored in `Exercise_8_12_more` / `Exercise_8_27`;
this is only the Scott-facing tip. -/
theorem exercise_8_12 :
    V.IsEffectivelyGiven ∧
      EffectivelyIsomorphic UComputablePresentation VComputablePresentation :=
  ⟨V_isEffectivelyGiven, ⟨effectiveIso812_UV⟩⟩

end DomainTheory.NeighbourhoodSystems
end
