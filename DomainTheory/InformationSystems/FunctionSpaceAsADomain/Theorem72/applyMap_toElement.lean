/-ai
Scott's Theorem 7.2: application of the application map to the pair of a function-space element and an element equals the element obtained by applying the approximable map recovered from the function-space element.

Both inclusions are checked. A token in the application image comes from a product set inside the pair and a function entailment. The tokens of that entailment lie in the function-space element and the input data lie in the argument, so closure produces the function token with the input union as input and the singleton as output, which is the recovered relation. Conversely, that recovered token is placed in the product by the lifted pair of its singleton with its input. Product consistency, containment in the pair, and a function entailment of that singleton — using consistency of tokens from the element, membership in the first component, reflexive entailment of the input by the second component, and reflexivity of the output singleton — witness the application relation.
ai-/
module

public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace
public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition53
public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition55
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Proposition62
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid32
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Theorem72.Basic
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Theorem72.mkFunToken_eq
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Theorem72.mem_fst_of_subset_pairElements
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Theorem72.mem_snd_of_subset_pairElements
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Theorem72.subset_pairElements_liftPair

@[expose] public section


namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

universe u v w

variable {α : Type u} {β : Type v} {γ : Type w}
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]
variable (A : InfoSys α) (B : InfoSys β) (C : InfoSys γ)


open ApproximableMap


/-- **Theorem 7.2.** `apply(g, y) = g(y)`. -/
theorem applyMap_toElement (g : (functionSystem B C).Element) (y : B.Element) :
    (applyMap (B := B) (C := C)).toElement
      (pairElements (functionSystem B C) B g y) =
      (element_toApproxMap B C g).toElement y := by
  apply le_antisymm
  · intro Z ⟨s, hs, ⟨hCon, hZcon, hEnt⟩⟩
    obtain ⟨hw, t, ht, hIn, hOut⟩ := hEnt
    have ht_sub : ↑t ⊆ g.carrier := by
      intro p hp
      exact mem_fst_of_subset_pairElements (functionSystem B C) B hs (ht (Finset.mem_coe.1 hp))
    have hsnd_sub : ↑(sndFinset (functionSystem B C) B s) ⊆ y.carrier := by
      intro b hb
      exact mem_snd_of_subset_pairElements (functionSystem B C) B hs hb
    have hin : funInputUnion B C t ∈ B.Con :=
      B.con_subset
        (proposition_2_3_ii B hCon.2 (entSet_inputUnion_of_ent B C hIn))
        (subset_funion_right _ _)
    have hin_sub : ↑(funInputUnion B C t) ⊆ y.carrier := by
      intro b hb
      rcases (mem_funInputUnion B C).1 (Finset.mem_coe.1 hb) with ⟨q, hq, hb'⟩
      exact y.closed _ b hsnd_sub (hIn q hq b hb')
    have hEntZ : FunEnt B C t
        (mkFunToken B C (funInputUnion B C t) {Z} hin (C.con_sing Z)) := by
      refine ⟨fun s' hs' hin' => hw s' (fun q hq => ht (hs' hq)) hin', t, Finset.Subset.refl _, ?_, hOut⟩
      intro q hq y' hy'
      exact B.ent_refl hin ((mem_funInputUnion B C).2 ⟨q, hq, hy'⟩)
    have hmem : mkFunToken B C (funInputUnion B C t) {Z} hin (C.con_sing Z) ∈ g.carrier :=
      g.closed t _ ht_sub hEntZ
    exact ⟨funInputUnion B C t, hin_sub, ⟨hin, C.con_sing Z, hmem⟩⟩
  · intro Z ⟨v, hv, ⟨hvCon, hZcon, hmem⟩⟩
    let p : FunToken B C := mkFunToken B C v {Z} hvCon hZcon
    have hp : p ∈ g.carrier := hmem
    let s := liftPair (functionSystem B C) B {p} v
    have hsCon : ProdCon (functionSystem B C) B s :=
      ProdCon_liftPair (functionSystem B C) B ((functionSystem B C).con_sing p) hvCon
    have hs_sub : ↑s ⊆ (pairElements (functionSystem B C) B g y).carrier :=
      subset_pairElements_liftPair (functionSystem B C) B
        (by
          intro q hq
          have : q = p := Finset.mem_singleton.mp (Finset.mem_coe.1 hq)
          subst this
          exact hp)
        hv
    refine ⟨s, hs_sub, ⟨hsCon, C.con_sing Z, ?_⟩⟩
    refine ⟨?_, {p}, ?_, ?_, ?_⟩
    · -- FunCon of fst s from g.consistent
      intro t ht hin
      have ht_sub : ↑t ⊆ g.carrier := by
        intro q hq
        exact mem_fst_of_subset_pairElements (functionSystem B C) B hs_sub (ht hq)
      exact (funCon_of_approxMap B C (element_toApproxMap B C g) t
        (fun q hq => ⟨q.property.1, q.property.2, by
          simpa [mkFunToken_eq] using ht_sub (Finset.mem_coe.2 hq)⟩)) t (Finset.Subset.refl _) hin
    · -- {p} ⊆ fst s
      intro q hq
      have : q = p := Finset.mem_singleton.mp hq
      subst this
      rw [show s = liftLeft (functionSystem B C) B {p} ∪' liftRight (functionSystem B C) B v from rfl]
      rw [fstFinset_funion, fstFinset_liftLeft]
      exact subset_funion_left _ _ (Finset.mem_singleton_self _)
    · -- snd s ⊢ v = p.input
      intro q hq
      have : q = p := Finset.mem_singleton.mp hq
      subst this
      intro b hb
      have hb' : b ∈ v := hb
      -- snd s = snd(liftLeft) ∪' v entails v
      have : b ∈ sndFinset (functionSystem B C) B s := by
        rw [sndFinset_liftPair]
        exact subset_funion_right _ _ hb'
      exact B.ent_refl hsCon.2 this
    · -- output {Z} ⊢ {Z}
      rw [funOutputUnion_singleton]
      exact proposition_2_3_iii C (C.con_sing Z)

end InfoSys
end DomainTheory.InformationSystems
