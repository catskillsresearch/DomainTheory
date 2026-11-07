module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.numberDomain
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.fixMap
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Proposition_2_6
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.cond
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.bot_le
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Proposition_3_9
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Theorem_3_12
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Theorem_3_13
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Lemma_3_6

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.NumRecSchemes
open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap
open DomainTheory.NeighbourhoodSystems.NatDom (N natElem zeroElt succMap predMap zeroMap
  succMap_natElem succMap_bot predMap_natElem_succ predMap_natElem_zero predMap_bot
  zeroMap_natElem_zero zeroMap_natElem_succ zeroMap_bot constLiftN constLiftN_natElem)
open DomainTheory.NeighbourhoodSystems.Exercise326 (cond)

def kSel : ApproximableMap (prod (funSpace (prod N N) N) (prod N N)) (funSpace (prod N N) N) :=
  proj₀ (funSpace (prod N N) N) (prod N N)

def qSel : ApproximableMap (prod (funSpace (prod N N) N) (prod N N)) (prod N N) :=
  proj₁ (funSpace (prod N N) N) (prod N N)

def argX : ApproximableMap (prod (funSpace (prod N N) N) (prod N N)) N := (proj₀ N N).comp qSel

def argY : ApproximableMap (prod (funSpace (prod N N) N) (prod N N)) N := (proj₁ N N).comp qSel

def strictId : ApproximableMap N N :=
  (cond N).comp (paired zeroMap (paired (idMap N) (idMap N)))

def strictProj₀ : ApproximableMap (prod N N) N :=
  (cond N).comp
    (paired (zeroMap.comp (proj₁ N N))
      (paired (proj₀ N N) (proj₀ N N)))

theorem T_bot_eq : (NatDom.T).bot = Truth.botElt :=
  le_antisymm ((NatDom.T).bot_le _) (Truth.botElt_le _)

section Mu
variable (f : ApproximableMap (prod N N) N)

def muBody : ApproximableMap (prod (funSpace (prod N N) N) (prod N N)) N :=
  (cond N).comp
    (paired (zeroMap.comp (f.comp qSel))
      (paired argX
        ((evalMap (prod N N) N).comp
          (paired kSel (paired (succMap.comp argX) argY)))))

def muOp : ApproximableMap (funSpace (prod N N) N) (funSpace (prod N N) N) :=
  curry (muBody f)

def muRec : ApproximableMap (prod N N) N := toApproxMap (muOp f).fixElement

def muMap : ApproximableMap N N := muRec f |>.comp (paired (constLiftN N (fun _ => zeroElt)) (idMap N))

theorem muBody_apply (k : (funSpace (prod N N) N).Element) (x y : N.Element) :
    (muBody f).toElementMap (pair k (pair x y)) =
      (cond N).toElementMap
        (pair (zeroMap.toElementMap (f.toElementMap (pair x y)))
          (pair x ((toApproxMap k).toElementMap (pair (succMap.toElementMap x) y)))) := by
  rw [muBody, toElementMap_comp]
  simp only [argX, argY, kSel, qSel, toElementMap_paired, toElementMap_comp, toElementMap_proj₀,
    toElementMap_proj₁, fst_pair, snd_pair, evalMap_apply]

theorem muMap_natElem (m : ℕ) :
    (muMap f).toElementMap (natElem m) = (muRec f).toElementMap (pair zeroElt (natElem m)) := by
  rw [muMap, toElementMap_comp, toElementMap_paired, toElementMap_idMap,
    constLiftN_natElem]

theorem muRec_rec (x y : N.Element) :
    (muRec f).toElementMap (pair x y) =
      (cond N).toElementMap
        (pair (zeroMap.toElementMap (f.toElementMap (pair x y)))
          (pair x ((muRec f).toElementMap (pair (succMap.toElementMap x) y)))) := by
  have hfix : (muOp f).toElementMap (muOp f).fixElement = (muOp f).fixElement :=
    toElementMap_fixElement (muOp f)
  have hval := toElementMap_curry_apply (muBody f) (muOp f).fixElement (pair x y)
  rw [← muOp, hfix] at hval
  rw [muRec, hval, muBody_apply]

theorem muRec_bot {n m : ℕ}
    (h : f.toElementMap (pair (natElem n) (natElem m)) = N.bot) :
    (muRec f).toElementMap (pair (natElem n) (natElem m)) = N.bot := by
  rw [muRec_rec, h, zeroMap_bot, T_bot_eq, Exercise326.cond_bot]

theorem muRec_found {n m : ℕ}
    (h : f.toElementMap (pair (natElem n) (natElem m)) = natElem 0) :
    (muRec f).toElementMap (pair (natElem n) (natElem m)) = natElem n := by
  rw [muRec_rec, h, zeroMap_natElem_zero, Exercise326.cond_true]

theorem muRec_step {n m j : ℕ}
    (h : f.toElementMap (pair (natElem n) (natElem m)) = natElem (j + 1)) :
    (muRec f).toElementMap (pair (natElem n) (natElem m)) =
      (muRec f).toElementMap (pair (natElem (n + 1)) (natElem m)) := by
  rw [muRec_rec, h, zeroMap_natElem_succ, Exercise326.cond_false, succMap_natElem]

theorem muRec_climb (m : ℕ) :
    ∀ (k n : ℕ), (∀ i < k, ∃ j, f.toElementMap (pair (natElem (n + i)) (natElem m)) = natElem (j + 1)) →
      (muRec f).toElementMap (pair (natElem n) (natElem m)) =
        (muRec f).toElementMap (pair (natElem (n + k)) (natElem m)) := by
  intro k
  induction k with
  | zero => intro n _; rw [Nat.add_zero]
  | succ k ih =>
    intro n h
    obtain ⟨j, hj⟩ := h 0 (Nat.succ_pos k)
    rw [Nat.add_zero] at hj
    have key := ih (n + 1) (fun i hi => by
      obtain ⟨j', hj'⟩ := h (i + 1) (by omega)
      exact ⟨j', by rw [show n + 1 + i = n + (i + 1) by omega]; exact hj'⟩)
    rw [muRec_step f hj, key, show n + 1 + k = n + (k + 1) by omega]

theorem muMap_eq_least {m n₀ : ℕ}
    (hzero : f.toElementMap (pair (natElem n₀) (natElem m)) = natElem 0)
    (hpos : ∀ i < n₀, ∃ j, f.toElementMap (pair (natElem i) (natElem m)) = natElem (j + 1)) :
    (muMap f).toElementMap (natElem m) = natElem n₀ := by
  rw [muMap_natElem]
  have hclimb := muRec_climb f m n₀ 0 (by simpa using hpos)
  rw [show (zeroElt : N.Element) = natElem 0 from rfl, hclimb, Nat.zero_add]
  exact muRec_found f hzero

end Mu

section PrimRec
variable (f : ApproximableMap N N) (g : ApproximableMap (prod N (prod N N)) N)

def primBody : ApproximableMap (prod (funSpace (prod N N) N) (prod N N)) N :=
  (cond N).comp
    (paired (zeroMap.comp argX)
      (paired (f.comp argY)
        (g.comp
          (paired (predMap.comp argX)
            (paired argY
              ((evalMap (prod N N) N).comp
                (paired kSel (paired (predMap.comp argX) argY))))))))

def primOp : ApproximableMap (funSpace (prod N N) N) (funSpace (prod N N) N) :=
  curry (primBody f g)

def primRec : ApproximableMap (prod N N) N := toApproxMap (primOp f g).fixElement

theorem primBody_apply (k : (funSpace (prod N N) N).Element) (x y : N.Element) :
    (primBody f g).toElementMap (pair k (pair x y)) =
      (cond N).toElementMap
        (pair (zeroMap.toElementMap x)
          (pair (f.toElementMap y)
            (g.toElementMap
              (pair (predMap.toElementMap x)
                (pair y ((toApproxMap k).toElementMap
                  (pair (predMap.toElementMap x) y))))))) := by
  rw [primBody, toElementMap_comp]
  simp only [argX, argY, kSel, qSel, toElementMap_paired, toElementMap_comp, toElementMap_proj₀,
    toElementMap_proj₁, fst_pair, snd_pair, evalMap_apply]

theorem primRec_rec (x y : N.Element) :
    (primRec f g).toElementMap (pair x y) =
      (cond N).toElementMap
        (pair (zeroMap.toElementMap x)
          (pair (f.toElementMap y)
            (g.toElementMap
              (pair (predMap.toElementMap x)
                (pair y ((primRec f g).toElementMap
                  (pair (predMap.toElementMap x) y))))))) := by
  have hfix : (primOp f g).toElementMap (primOp f g).fixElement = (primOp f g).fixElement :=
    toElementMap_fixElement (primOp f g)
  have hval := toElementMap_curry_apply (primBody f g) (primOp f g).fixElement (pair x y)
  rw [← primOp, hfix] at hval
  rw [primRec, hval, primBody_apply]

theorem primRec_bot (m : ℕ) :
    (primRec f g).toElementMap (pair N.bot (natElem m)) = N.bot := by
  rw [primRec_rec, zeroMap_bot, T_bot_eq, Exercise326.cond_bot]

theorem primRec_succ (n m : ℕ) :
    (primRec f g).toElementMap (pair (natElem (n + 1)) (natElem m)) =
      g.toElementMap
        (pair (natElem n)
          (pair (natElem m) ((primRec f g).toElementMap (pair (natElem n) (natElem m))))) := by
  rw [primRec_rec, zeroMap_natElem_succ, Exercise326.cond_false, predMap_natElem_succ]

theorem primRec_zero (m : ℕ) :
    (primRec f g).toElementMap (pair (natElem 0) (natElem m)) = f.toElementMap (natElem m) := by
  rw [primRec_rec, zeroMap_natElem_zero, Exercise326.cond_true]

end PrimRec

theorem strictId_bot : strictId.toElementMap N.bot = N.bot := by
  rw [strictId, toElementMap_comp]
  simp only [toElementMap_paired, toElementMap_idMap]
  rw [zeroMap_bot, T_bot_eq, Exercise326.cond_bot]

theorem strictId_natElem (n : ℕ) : strictId.toElementMap (natElem n) = natElem n := by
  rw [strictId, toElementMap_comp]
  simp only [toElementMap_paired, toElementMap_idMap]
  cases n with
  | zero => rw [zeroMap_natElem_zero, Exercise326.cond_true]
  | succ k => rw [zeroMap_natElem_succ, Exercise326.cond_false]

theorem strictProj₀_apply (x y : N.Element) :
    strictProj₀.toElementMap (pair x y) =
      (cond N).toElementMap (pair (zeroMap.toElementMap y) (pair x x)) := by
  rw [strictProj₀, toElementMap_comp]
  simp only [toElementMap_paired, toElementMap_comp, toElementMap_proj₀, toElementMap_proj₁,
    fst_pair, snd_pair]

theorem strictProj₀_bot_left (m : ℕ) :
    strictProj₀.toElementMap (pair N.bot (natElem m)) = N.bot := by
  rw [strictProj₀_apply]
  cases m with
  | zero => rw [zeroMap_natElem_zero, Exercise326.cond_true]
  | succ k => rw [zeroMap_natElem_succ, Exercise326.cond_false]

theorem strictProj₀_bot_right (n : ℕ) :
    strictProj₀.toElementMap (pair (natElem n) N.bot) = N.bot := by
  rw [strictProj₀_apply, zeroMap_bot, T_bot_eq, Exercise326.cond_bot]

theorem strictProj₀_natElem (n m : ℕ) :
    strictProj₀.toElementMap (pair (natElem n) (natElem m)) = natElem n := by
  rw [strictProj₀_apply]
  cases m with
  | zero => rw [zeroMap_natElem_zero, Exercise326.cond_true]
  | succ k => rw [zeroMap_natElem_succ, Exercise326.cond_false]

end DomainTheory.NeighbourhoodSystems.NumRecSchemes
