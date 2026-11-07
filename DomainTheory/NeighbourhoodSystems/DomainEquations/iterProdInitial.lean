module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.strictDomainObj
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.iterSys
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.prodFunctor
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.iSupMap
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.ofIso
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Theorem_6_16
public import DomainTheory.NeighbourhoodSystems.DomainEquations.talgebra
public import DomainTheory.NeighbourhoodSystems.DomainEquations.endofunctor
public import DomainTheory.NeighbourhoodSystems.DomainEquations.cAlgebra
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.supChain

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems
open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.SmashProduct

section
namespace Exercise618

variable {α : Type*} {V : NeighborhoodSystem α}

def consSeq (a : V.Element) (b : (iterSys V).Element) : ℕ → V.Element :=
  fun i => Nat.casesOn i a (fun k => component b k)

@[simp] theorem consSeq_zero (a : V.Element) (b : (iterSys V).Element) : consSeq a b 0 = a := rfl

@[simp] theorem consSeq_succ (a : V.Element) (b : (iterSys V).Element) (k : ℕ) :
    consSeq a b (k + 1) = component b k := rfl

theorem iterBot_eq : (iterSys V).bot = ofSeq (fun _ : ℕ => V.bot) := by
  apply Element.ext
  intro W
  rw [mem_bot, mem_ofSeq]
  constructor
  · rintro rfl
    refine ⟨(iterSys V).master_mem, fun i => ?_⟩
    rw [fiber_iterSys_master, mem_bot]
  · rintro ⟨_, hfib⟩
    apply eq_of_fiber_eq
    intro i
    have hi := hfib i
    rw [fiber_iterSys_master]
    rwa [mem_bot] at hi

@[simp] theorem component_bot (n : ℕ) : component (iterSys V).bot n = V.bot := by
  rw [iterBot_eq, component_ofSeq]

theorem chain_le_of_succ {β : Type*} {W : NeighborhoodSystem β} {a : ℕ → W.Element}
    (h : ∀ n, a n ≤ a (n + 1)) {i j : ℕ} (hij : i ≤ j) : a i ≤ a j := by
  induction hij with
  | refl => exact le_rfl
  | step _ ih => exact ih.trans (h _)

section Target

variable {γ : Type*} {E : NeighborhoodSystem γ}

theorem constBot_le (f : ApproximableMap (iterSys V) E) :
    constMap (iterSys V) E.bot ≤ f := by
  intro X Y hrel
  obtain ⟨hX, hY⟩ := hrel
  rw [mem_bot] at hY; subst hY
  exact f.rel_master hX

end Target

def imap (V : NeighborhoodSystem α) : ApproximableMap (prod V (iterSys V)) (iterSys V) :=
  ofIso (iterProdIso V).symm

theorem isStrict_imap : IsStrict (imap V) := isStrict_ofIso _

theorem iterProdIso_apply (z : (iterSys V).Element) :
    iterProdIso V z = pair (component z 0) (ofSeq (fun n => component z (n + 1))) := rfl

theorem iterProdIso_symm_pair (a : V.Element) (b : (iterSys V).Element) :
    (iterProdIso V).symm (pair a b) = ofSeq (consSeq a b) := by
  have hkey : iterProdIso V (ofSeq (consSeq a b)) = pair a b := by
    rw [iterProdIso_apply]
    congr 1
    · rw [component_ofSeq, consSeq_zero]
    · have : (fun n => component (ofSeq (consSeq a b)) (n + 1)) = fun n => component b n := by
        funext n; rw [component_ofSeq, consSeq_succ]
      rw [this, ofSeq_component]
  rw [← hkey, OrderIso.symm_apply_apply]

end Exercise618
end

section
namespace Exercise618

theorem iterSys_nonempty {α : Type*} {V : NeighborhoodSystem α}
    (h : ∀ X, V.mem X → X.Nonempty) :
    ∀ W, (iterSys V).mem W → W.Nonempty := by
  rintro W ⟨hfib, _⟩
  obtain ⟨a, ha⟩ := h (fiber W 0) (hfib 0)
  exact ⟨(0, a), ha⟩

end Exercise618
end

section
namespace Exercise618

variable {α : Type*} {V : NeighborhoodSystem α}

def iterObj (Dom : StrictDomainObj.{w}) : StrictDomainObj.{w} where
  carrier := ℕ × Dom.carrier
  sys := iterSys Dom.sys
  nonempty := iterSys_nonempty Dom.nonempty

def jmap (V : NeighborhoodSystem α) : ApproximableMap (iterSys V) (prod V (iterSys V)) :=
  ofIso (iterProdIso V)

section Target

variable {γ : Type*} {E : NeighborhoodSystem γ}

def descOp (k : ApproximableMap (prod V E) E) (f : ApproximableMap (iterSys V) E) :
    ApproximableMap (iterSys V) E :=
  k.comp ((prodMap (idMap V) f).comp (jmap V))

theorem descOp_apply (k : ApproximableMap (prod V E) E) (f : ApproximableMap (iterSys V) E)
    (z : (iterSys V).Element) :
    (descOp k f).toElementMap z
      = k.toElementMap (pair (component z 0)
          (f.toElementMap (ofSeq (fun n => component z (n + 1))))) := by
  simp only [descOp, jmap]
  rw [toElementMap_comp, toElementMap_comp, toElementMap_ofIso, iterProdIso_apply,
    toElementMap_prodMap_pair, toElementMap_idMap]

def descSeq (k : ApproximableMap (prod V E) E) : ℕ → ApproximableMap (iterSys V) E
  | 0 => constMap (iterSys V) E.bot
  | (n + 1) => descOp k (descSeq k n)

end Target

section Uniq

variable {γ : Type*} {E : NeighborhoodSystem γ}

theorem gcomp_rho_succ (k : ApproximableMap (prod V E) E) (g : ApproximableMap (iterSys V) E)
    (hc : g.comp (imap V) = k.comp (prodMap (idMap V) g)) (n : ℕ) :
    g.comp (descSeq (imap V) (n + 1)) = descOp k (g.comp (descSeq (imap V) n)) := by
  show g.comp ((imap V).comp ((prodMap (idMap V) (descSeq (imap V) n)).comp (jmap V)))
     = k.comp ((prodMap (idMap V) (g.comp (descSeq (imap V) n))).comp (jmap V))
  rw [← comp_assoc, hc, comp_assoc]
  congr 1
  rw [← comp_assoc, ← prodMap_comp, idMap_comp]

theorem gcomp_rho_zero (g : ApproximableMap (iterSys V) E) (hg : IsStrict g) :
    g.comp (descSeq (imap V) 0) = constMap (iterSys V) E.bot := by
  apply ext_of_toElementMap
  intro x
  rw [toElementMap_comp, toElementMap_constMap,
    show descSeq (imap V) 0 = constMap (iterSys V) (iterSys V).bot from rfl,
    toElementMap_constMap, isStrict_iff_apply_bot.mp hg]

end Uniq

theorem jmap_comp_imap : (jmap V).comp (imap V) = idMap (prod V (iterSys V)) := by
  apply ext_of_toElementMap
  intro w
  simp only [jmap, imap]
  rw [toElementMap_comp, toElementMap_ofIso, toElementMap_ofIso, toElementMap_idMap,
    OrderIso.apply_symm_apply]

section Target

variable {γ : Type*} {E : NeighborhoodSystem γ}

def kHead (k : ApproximableMap (prod V E) E) (a : V.Element) :
    ApproximableMap E E :=
  k.comp (paired (constMap E a) (idMap E))

theorem kHead_apply (k : ApproximableMap (prod V E) E) (a : V.Element) (u : E.Element) :
    (kHead k a).toElementMap u = k.toElementMap (pair a u) := by
  rw [kHead, toElementMap_comp, toElementMap_paired, toElementMap_constMap, toElementMap_idMap]

end Target

theorem pair_bot {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} :
    pair V₀.bot V₁.bot = (prod V₀ V₁).bot := by
  apply Element.ext
  intro W
  rw [mem_bot, prod_master]
  constructor
  · rintro ⟨X, Y, hX, hY, rfl⟩
    rw [mem_bot] at hX hY; subst hX; subst hY; rfl
  · rintro rfl
    exact ⟨V₀.master, V₁.master, V₀.bot.master_mem, V₁.bot.master_mem, rfl⟩

section Target

variable {γ : Type*} {E : NeighborhoodSystem γ}

theorem descSeq_strict (k : ApproximableMap (prod V E) E) (hk : IsStrict k) :
    ∀ n, IsStrict (descSeq k n)
  | 0 => isStrict_constBot
  | (n + 1) => by
      have ih := descSeq_strict k hk n
      rw [isStrict_iff_apply_bot] at ih ⊢
      rw [show descSeq k (n + 1) = descOp k (descSeq k n) from rfl, descOp_apply]
      have htl : ofSeq (fun m => component (iterSys V).bot (m + 1)) = (iterSys V).bot := by
        have hconst : (fun m => component (iterSys V).bot (m + 1)) = (fun _ => V.bot) := by
          funext m; rw [component_bot]
        rw [hconst, ← iterBot_eq]
      rw [component_bot, htl, ih, pair_bot]
      exact isStrict_iff_apply_bot.mp hk

end Target

theorem isStrict_prodMap {α β α' β' : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
    {V₀' : NeighborhoodSystem α'} {V₁' : NeighborhoodSystem β'}
    {f₀ : ApproximableMap V₀ V₀'} {f₁ : ApproximableMap V₁ V₁'}
    (hf₀ : IsStrict f₀) (hf₁ : IsStrict f₁) : IsStrict (prodMap f₀ f₁) := by
  rw [isStrict_iff_apply_bot, show (prod V₀ V₁).bot = pair V₀.bot V₁.bot from pair_bot.symm,
    toElementMap_prodMap_pair, isStrict_iff_apply_bot.mp hf₀, isStrict_iff_apply_bot.mp hf₁]
  exact pair_bot

end Exercise618
end

end DomainTheory.NeighbourhoodSystems
namespace DomainTheory.NeighbourhoodSystems
section
open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.SmashProduct

namespace Exercise618

variable {α : Type*} {V : NeighborhoodSystem α}

theorem prodMap_idMap_mono {γ : Type*} {E : NeighborhoodSystem γ}
    {f f' : ApproximableMap (iterSys V) E} (h : f ≤ f') :
    prodMap (idMap V) f ≤ prodMap (idMap V) f' := by
  intro W P hrel
  simp only [prodMap, paired_rel] at hrel ⊢
  exact ⟨hrel.1, hrel.2.1, comp_mono_gen h le_rfl _ _ hrel.2.2⟩

section Target

variable {γ : Type*} {E : NeighborhoodSystem γ}

theorem descOp_mono (k : ApproximableMap (prod V E) E) {f f' : ApproximableMap (iterSys V) E}
    (h : f ≤ f') : descOp k f ≤ descOp k f' :=
  comp_mono_gen le_rfl (comp_mono_gen (prodMap_idMap_mono h) le_rfl)

theorem descSeq_mono_succ (k : ApproximableMap (prod V E) E) (n : ℕ) :
    descSeq k n ≤ descSeq k (n + 1) := by
  induction n with
  | zero => exact constBot_le _
  | succ m ih => exact descOp_mono k ih

theorem descSeq_mono (k : ApproximableMap (prod V E) E) {n m : ℕ} (h : n ≤ m) :
    descSeq k n ≤ descSeq k m := by
  induction h with
  | refl => exact le_rfl
  | step _ ih => exact ih.trans (descSeq_mono_succ k _)

theorem descSeq_dir (k : ApproximableMap (prod V E) E) :
    ∀ i j, ∃ l, (∀ X Y, (descSeq k i).rel X Y → (descSeq k l).rel X Y) ∧
      (∀ X Y, (descSeq k j).rel X Y → (descSeq k l).rel X Y) :=
  fun i j => ⟨max i j, fun _ _ => descSeq_mono k (le_max_left i j) _ _,
    fun _ _ => descSeq_mono k (le_max_right i j) _ _⟩

def descMap (k : ApproximableMap (prod V E) E) : ApproximableMap (iterSys V) E :=
  iSupMap (descSeq k) (descSeq_dir k)

theorem descMap_toElementMap (k : ApproximableMap (prod V E) E) (z : (iterSys V).Element)
    {Y : Set γ} :
    ((descMap k).toElementMap z).mem Y ↔ ∃ n, ((descSeq k n).toElementMap z).mem Y :=
  mem_toElementMap_iSupMap (descSeq k) (descSeq_dir k) z

theorem descMap_strict (k : ApproximableMap (prod V E) E) (hk : IsStrict k) :
    IsStrict (descMap k) := by
  rw [isStrict_iff_apply_bot]
  apply Element.ext
  intro Y
  rw [mem_bot, descMap_toElementMap]
  constructor
  · rintro ⟨n, hn⟩
    have hs := descSeq_strict k hk n
    rw [isStrict_iff_apply_bot] at hs
    rw [hs, mem_bot] at hn
    exact hn
  · rintro rfl
    have hs := descSeq_strict k hk 0
    rw [isStrict_iff_apply_bot] at hs
    exact ⟨0, by rw [hs]; exact E.bot.master_mem⟩

end Target

end Exercise618
end

section
open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.SmashProduct

namespace Exercise618

theorem prod_nonempty {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
    (h₀ : ∀ X, V₀.mem X → X.Nonempty) (_h₁ : ∀ Y, V₁.mem Y → Y.Nonempty) :
    ∀ W, (prod V₀ V₁).mem W → W.Nonempty := by
  rintro W ⟨X, Y, hX, _, rfl⟩
  obtain ⟨a, ha⟩ := h₀ X hX
  exact ⟨Sum.inl a, prodNbhd.mem_inl.mpr ha⟩

end Exercise618
end

section
open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.SmashProduct

namespace Exercise618

variable {α : Type*} {V : NeighborhoodSystem α}

def prodObj (Dom X : StrictDomainObj.{w}) : StrictDomainObj.{w} where
  carrier := Dom.carrier ⊕ X.carrier
  sys := prod Dom.sys X.sys
  nonempty := prod_nonempty Dom.nonempty X.nonempty

def prodMapHom (Dom : StrictDomainObj.{w}) {X Y : StrictDomainObj.{w}} (f : (X ⟶ Y)) :
    ((prodObj Dom X) ⟶ (prodObj Dom Y)) :=
  ⟨prodMap (idMap Dom.sys) f.1, isStrict_prodMap isStrict_idMap f.2⟩

def prodFunctor (Dom : StrictDomainObj.{w}) : Endofunctor StrictDomainObj.{w} where
  obj := prodObj Dom
  map := prodMapHom Dom
  map_id X := Subtype.ext (by
    show prodMap (idMap Dom.sys) (idMap X.sys) = idMap (prod Dom.sys X.sys)
    exact prodMap_id)
  map_comp {X Y Z} g f := Subtype.ext (by
    show prodMap (idMap Dom.sys) (g.1.comp f.1)
       = (prodMap (idMap Dom.sys) g.1).comp (prodMap (idMap Dom.sys) f.1)
    have h := prodMap_comp (idMap Dom.sys) (idMap Dom.sys) g.1 f.1
    rw [idMap_comp] at h
    exact h)

def iterAlg (Dom : StrictDomainObj.{w}) : TAlgebra (prodFunctor Dom) where
  carrier := iterObj Dom
  str := ⟨imap Dom.sys, isStrict_imap⟩

theorem rho_apply (n : ℕ) (z : (iterSys V).Element) :
    (descSeq (imap V) n).toElementMap z
      = ofSeq (fun i => if i < n then component z i else V.bot) := by
  induction n generalizing z with
  | zero =>
    show (constMap (iterSys V) (iterSys V).bot).toElementMap z = _
    rw [toElementMap_constMap, iterBot_eq]
    congr 1
  | succ n ih =>
    rw [show descSeq (imap V) (n + 1) = descOp (imap V) (descSeq (imap V) n) from rfl,
      descOp_apply, ih]
    simp only [imap]
    rw [toElementMap_ofIso, iterProdIso_symm_pair]
    congr 1
    funext j
    cases j with
    | zero =>
      show component z 0 = if (0 : ℕ) < n + 1 then component z 0 else V.bot
      rw [ite_eq_left (Nat.zero_lt_succ n)]
    | succ k =>
      rw [consSeq_succ, component_ofSeq, component_ofSeq]
      show (if k < n then component z (k + 1) else V.bot)
         = if k + 1 < n + 1 then component z (k + 1) else V.bot
      by_cases h : k < n
      · rw [ite_eq_left h, ite_eq_left (Nat.succ_lt_succ h)]
      · rw [ite_eq_right h, ite_eq_right (fun hc => h (Nat.lt_of_succ_lt_succ hc))]

theorem iSupRho_eq_id : descMap (imap V) = idMap (iterSys V) := by
  apply ext_of_toElementMap
  intro z
  rw [toElementMap_idMap]
  apply Element.ext
  intro Y
  rw [descMap_toElementMap]
  constructor
  · rintro ⟨n, hn⟩
    have hle : (descSeq (imap V) n).toElementMap z ≤ z := by
      rw [rho_apply]
      have hz : z = ofSeq (fun i => component z i) := (ofSeq_component z).symm
      conv_rhs => rw [hz]
      apply ofSeq_mono
      intro i
      show (if i < n then component z i else V.bot) ≤ component z i
      split
      · exact le_rfl
      · exact V.bot_le _
    exact hle Y hn
  · intro hzY
    have hY : (iterSys V).mem Y := z.sub hzY
    obtain ⟨N, hN⟩ := hY.2
    have hcomp : ∀ i, (component z i).mem (fiber Y i) := by
      have h := hzY
      rw [← ofSeq_component z] at h
      rw [mem_ofSeq] at h
      exact h.2
    refine ⟨N, ?_⟩
    rw [rho_apply, mem_ofSeq]
    refine ⟨hY, fun i => ?_⟩
    show (if i < N then component z i else V.bot).mem (fiber Y i)
    by_cases h : i < N
    · rw [ite_eq_left h]; exact hcomp i
    · rw [ite_eq_right h, hN i (not_lt.mp h)]; exact V.bot.master_mem

section Uniq

variable {γ : Type*} {E : NeighborhoodSystem γ}

theorem comm_unique (k : ApproximableMap (prod V E) E)
    {g g' : ApproximableMap (iterSys V) E} (hg : IsStrict g) (hg' : IsStrict g')
    (hc : g.comp (imap V) = k.comp (prodMap (idMap V) g))
    (hc' : g'.comp (imap V) = k.comp (prodMap (idMap V) g')) : g = g' := by
  have hindep : ∀ n, g.comp (descSeq (imap V) n) = g'.comp (descSeq (imap V) n) := by
    intro n
    induction n with
    | zero => rw [gcomp_rho_zero g hg, gcomp_rho_zero g' hg']
    | succ m ih => rw [gcomp_rho_succ k g hc m, gcomp_rho_succ k g' hc' m, ih]
  have key : g.comp (descMap (imap V)) = g'.comp (descMap (imap V)) := by
    apply ApproximableMap.ext
    intro X Z
    simp only [descMap, comp_rel]
    constructor
    · rintro ⟨Y, ⟨i, hXY⟩, hYZ⟩
      have hg : (g.comp (descSeq (imap V) i)).rel X Z := ⟨Y, hXY, hYZ⟩
      rw [hindep i] at hg
      obtain ⟨Y', hXY', hYZ'⟩ := hg
      exact ⟨Y', ⟨i, hXY'⟩, hYZ'⟩
    · rintro ⟨Y, ⟨i, hXY⟩, hYZ⟩
      have hg' : (g'.comp (descSeq (imap V) i)).rel X Z := ⟨Y, hXY, hYZ⟩
      rw [← hindep i] at hg'
      obtain ⟨Y', hXY', hYZ'⟩ := hg'
      exact ⟨Y', ⟨i, hXY'⟩, hYZ'⟩
  rw [iSupRho_eq_id] at key
  rwa [comp_idMap, comp_idMap] at key

end Uniq

theorem succChainDir {β : Type*} {W : NeighborhoodSystem β} (a : ℕ → W.Element)
    (h : ∀ n, a n ≤ a (n + 1)) : ∀ i j, ∃ l, a i ≤ a l ∧ a j ≤ a l :=
  fun i j => ⟨max i j, chain_le_of_succ h (le_max_left i j), chain_le_of_succ h (le_max_right i j)⟩

theorem toElementMap_le_of_le {β₀ β₁ : Type*} {W₀ : NeighborhoodSystem β₀}
    {W₁ : NeighborhoodSystem β₁} {f g : ApproximableMap W₀ W₁} (h : f ≤ g) (x : W₀.Element) :
    f.toElementMap x ≤ g.toElementMap x := by
  rintro Y ⟨X, hX, hrel⟩
  exact ⟨X, hX, h _ _ hrel⟩

section Target

variable {γ : Type*} {E : NeighborhoodSystem γ}

theorem descSeqEltMono (k : ApproximableMap (prod V E) E) (x : (iterSys V).Element) :
    ∀ n, (descSeq k n).toElementMap x ≤ (descSeq k (n + 1)).toElementMap x :=
  fun n => toElementMap_le_of_le (descSeq_mono_succ k n) x

theorem descMap_eq (k : ApproximableMap (prod V E) E) (x : (iterSys V).Element) :
    (descMap k).toElementMap x
      = iSupDirected (fun n => (descSeq k n).toElementMap x)
          (succChainDir _ (descSeqEltMono k x)) := by
  apply Element.ext
  intro Y
  rw [descMap_toElementMap, mem_iSupDirected]

theorem descMap_fix (k : ApproximableMap (prod V E) E) : descMap k = descOp k (descMap k) := by
  apply ext_of_toElementMap
  intro z
  rw [descOp_apply, descMap_eq k (ofSeq (fun n => component z (n + 1))),
    ← kHead_apply k (component z 0), toElementMap_iSupDirected, descMap_eq k z]

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

theorem descMap_comm (k : ApproximableMap (prod V E) E) :
    (descMap k).comp (imap V) = k.comp (prodMap (idMap V) (descMap k)) := by
  conv_lhs => rw [descMap_fix k]
  show (k.comp ((prodMap (idMap V) (descMap k)).comp (jmap V))).comp (imap V)
     = k.comp (prodMap (idMap V) (descMap k))
  rw [comp_assoc, comp_assoc, jmap_comp_imap, comp_idMap]

end Target

def descAlgHom (Dom : StrictDomainObj.{w}) (B : TAlgebra (prodFunctor Dom)) :
    AlgHom (iterAlg Dom) B where
  hom := ⟨descMap B.str.1, descMap_strict B.str.1 B.str.2⟩
  comm := by
    apply Subtype.ext
    show (descMap B.str.1).comp (imap Dom.sys)
       = B.str.1.comp (prodMap (idMap Dom.sys) (descMap B.str.1))
    exact descMap_comm B.str.1

end Exercise618
end
end DomainTheory.NeighbourhoodSystems
