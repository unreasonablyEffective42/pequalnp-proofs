import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
theorem PEqualNP.Outside.R_meta_7891_731
  (two : ∀ (pair : BitVec 30) (B : List (Bool × ℕ × ℕ)), pair ∈ [426545243,487490915,224826680] →
    B.length ≤ 16 →
    (32767 : BitVec 30) ∉ B.foldl (fun (ws : List (BitVec 30)) (g : Bool × ℕ × ℕ) => ws ++ [if g.1 then ws.getD g.2.1 0 ||| ws.getD g.2.2 0 else ws.getD g.2.1 0 &&& ws.getD g.2.2 0])
      ([41,419987523,608501894,169476628,23367704,201753888,3614784,28852608,834670080,1040216064] ++ [pair,493786491]))
  (late : let step := fun (ws : List (BitVec 30)) (g : Bool × ℕ × ℕ) => ws ++ [if g.1 then ws.getD g.2.1 0 ||| ws.getD g.2.2 0 else ws.getD g.2.1 0 &&& ws.getD g.2.2 0]
    ∀ A B : List (Bool × ℕ × ℕ), 3 ≤ A.length → 2 ≤ B.length → A.length + B.length ≤ 18 →
    let W := A.foldl step [0,419987523,608501894,169476628,23367704,201753888,3614784,28852608,834670080,1040216064]
    let d := W.getD (9+A.length) 0
    d &&& 41 = 41 →
    (32767 : BitVec 30) ∉ B.foldl step (W.set 0 (579928105 &&& d)))
  (last : ∀ A : List (Bool × ℕ × ℕ), A.length ≤ 17 →
    let W := A.foldl (fun (ws : List (BitVec 30)) (g : Bool × ℕ × ℕ) => ws ++ [if g.1 then ws.getD g.2.1 0 ||| ws.getD g.2.2 0 else ws.getD g.2.1 0 &&& ws.getD g.2.2 0]) [0,419987523,608501894,169476628,23367704,201753888,3614784,28852608,834670080,1040216064]
    let d := W.getD (9+A.length) 0
    d &&& 41 = 41 → 579928105 &&& d = 41 →
    ∀ h ∈ W, (41 ||| h : BitVec 30) ≠ 32767) :
  (∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : ℕ),   PEqualNP.TopForm.IsAO2 (10 : ℕ) x1 →     (16 : ℕ) ≤ x1.size ∧ x1.size ≤ (18 : ℕ) →       (x2 ≠ (0 : ℕ) ∧ x2 < (10 : ℕ) + x1.size ∧ ∀ (x5 : ℕ) (x6 : PEqualNP.CircuitLowerBounds.Gate), (10 : ℕ) + x5 ≤ x2 → x1.gates[x5]? = Option.some x6 → (0 : ℕ) ∉ x6.inputs) →         have x6 : ℕ → Fin (10 : ℕ) → Bool := fun (x6 : ℕ) (x7 : Fin (10 : ℕ)) => x6.testBit ↑x7;         have x7 : ℕ → Bool := fun (x7 : ℕ) => (x1.wires (List.ofFn (Function.update (x6 x7) (0 : Fin (10 : ℕ)) Bool.false))).getD x2 Bool.false;         have x8 : ℕ → Bool := fun (x8 : ℕ) => PEqualNP.MetaComplexity.circuitFun (10 : ℕ) x1 (Function.update (x6 x8) (0 : Fin (10 : ℕ)) (x6 x8 (0 : Fin (10 : ℕ)) && x7 x8));         (∀ x9 ∈ [(2 : ℕ), (16 : ℕ), (32 : ℕ)], x7 x9 = Bool.true) → ¬((∀ x10 ∈ [(3 : ℕ), (6 : ℕ), (12 : ℕ), (17 : ℕ), (24 : ℕ), (33 : ℕ), (66 : ℕ), (132 : ℕ), (160 : ℕ), (264 : ℕ), (288 : ℕ), (320 : ℕ), (528 : ℕ), (576 : ℕ), (640 : ℕ)], x8 x10 = Bool.true) ∧ ∀ x10 ∈ [(50 : ℕ), (69 : ℕ), (104 : ℕ), (116 : ℕ), (138 : ℕ), (201 : ℕ), (208 : ℕ), (276 : ℕ), (385 : ℕ), (402 : ℕ), (521 : ℕ), (548 : ℕ), (554 : ℕ), (770 : ℕ), (773 : ℕ)], x8 x10 = Bool.false)) := by
  intro C w shape sizes sched
  dsimp only
  intro neighbors tests
  let rows : List ℕ := [3,6,12,17,24,33,66,132,160,264,288,320,528,576,640,50,69,104,116,138,201,208,276,385,402,521,548,554,770,773]
  let row (r : ℕ) (i : Fin 10) := r.testBit i.val
  let off (r : ℕ) := Function.update (row r) (0 : Fin 10) false
  let guard (r : ℕ) := (C.wires (List.ofFn (off r))).getD w false
  let changed (r : ℕ) := Function.update (row r) (0 : Fin 10) (r.testBit 0 && guard r)
  let base : List (BitVec 30) := [0,419987523,608501894,169476628,23367704,201753888,3614784,28852608,834670080,1040216064]
  let put := fun (ws : List (BitVec 30)) (g : Bool × ℕ × ℕ) =>
    ws ++ [if g.1 then ws.getD g.2.1 0 ||| ws.getD g.2.2 0 else ws.getD g.2.1 0 &&& ws.getD g.2.2 0]
  let advance := fun (ws : List Bool) (g : Gate) => ws ++ [g.op.eval (g.inputs.map fun i => ws.getD i false)]
  let encode := fun (g : Gate) => (g.op.eval [true,false], g.inputs.getD 0 0, g.inputs.getD 1 0)
  let bit (i : Fin 30) (v : BitVec 30) := v.getLsbD i.val
  have project (i : Fin 30) (ws : List (BitVec 30)) (j : ℕ) :
      (ws.map (bit i)).getD j false = bit i (ws.getD j 0) := by
    have hz : bit i 0 = false := by simp [bit]
    rw [← hz,List.getD_map]
  have pair (g : Gate) (hg : g ∈ C.gates) : ∃ a b, g.inputs = [a,b] := by
    have h := shape.2.2 g hg
    cases h' : g.inputs with
    | nil => simp [h'] at h
    | cons a as =>
      cases as with
      | nil => simp [h'] at h
      | cons b bs =>
        cases bs with
        | nil => exact ⟨a,b,rfl⟩
        | cons c cs => simp [h'] at h
  have va (l : List Bool) : GateOp.and.eval l = l.all id := rfl
  have vo (l : List Bool) : GateOp.or.eval l = l.any id := rfl
  have simulate (gs : List Gate) (ok : ∀ g ∈ gs, g ∈ C.gates) (i : Fin 30) (ws : List (BitVec 30)) :
      ((gs.map encode).foldl put ws).map (bit i) = gs.foldl advance (ws.map (bit i)) := by
    induction gs generalizing ws with
    | nil => rfl
    | cons g gs ih =>
      have hg := ok g List.mem_cons_self
      obtain ⟨a,b,hab⟩ := pair g hg
      simp only [List.map_cons,List.foldl_cons]
      rw [ih (fun x hx => ok x (List.mem_cons_of_mem _ hx))]
      congr 1
      rcases shape.1 g hg with ho | ho <;>
        simp [put,advance,encode,ho,hab,va,vo,bit] <;>
        cases ws[a]? <;> cases ws[b]? <;> simp
  have extendsFold {α β : Type} (step : List α → β → α) (gs : List β) (ws : List α) :
      ∃ tail, gs.foldl (fun s g => s ++ [step s g]) ws = ws ++ tail ∧ tail.length = gs.length := by
    induction gs generalizing ws with
    | nil => exact ⟨[], by simp, rfl⟩
    | cons g gs ih =>
      obtain ⟨t,ht,hl⟩ := ih (ws ++ [step ws g])
      exact ⟨step ws g :: t,by simpa only [List.foldl_cons,List.append_assoc,List.singleton_append] using ht,by simp [hl]⟩
  let k := w+1-10
  let pre := C.gates.take k
  let post := C.gates.drop k
  let A := pre.map encode
  let B := post.map encode
  let W := A.foldl put base
  let d := W.getD w 0
  let z := (579928105 : BitVec 30) &&& d
  have concat : pre ++ post = C.gates := List.take_append_drop ..
  have preMem (g : Gate) (hg : g ∈ pre) : g ∈ C.gates := concat ▸ List.mem_append_left post hg
  have postMem (g : Gate) (hg : g ∈ post) : g ∈ C.gates := concat ▸ List.mem_append_right pre hg
  have sz : C.gates.length = C.size := rfl
  have hk : k ≤ C.gates.length := by have := sched.2.1; dsimp [k]; omega
  have lenA : A.length = k := by simp [A,pre,List.length_take,Nat.min_eq_left hk]
  have sum : A.length + B.length = C.size := by simpa [A,B,sz] using congrArg List.length concat
  have growth (s : List (BitVec 30)) (p : List (Bool × ℕ × ℕ)) :
      ∃ t, p.foldl put s = s ++ t ∧ t.length = p.length := extendsFold _ _ _
  have lengthW : W.length = 10 + k := by
    obtain ⟨t,h,ht⟩ := growth base A
    change (A.foldl put base).length = _
    rw [h,List.length_append,ht,lenA]
    rfl
  have wBound : w < W.length := by rw [lengthW]; dsimp [k]; omega
  have offInputs (i : Fin 30) : base.map (bit i) = List.ofFn (off (rows.get i)) := by
    revert i
    decide
  have probe (i : Fin 30) : bit i d = guard (rows.get i) := by
    have sim := simulate pre preMem i base
    rw [offInputs] at sim
    change W.map (bit i) = _ at sim
    change _ = (C.gates.foldl advance _).getD w false
    rw [← concat,List.foldl_append,← sim]
    obtain ⟨t,ht,_⟩ := extendsFold (fun s (g : Gate) => g.op.eval (g.inputs.map fun j => s.getD j false)) post (W.map (bit i))
    change post.foldl advance _ = _ at ht
    rw [ht,List.getD_append _ _ _ _ (by simpa using wBound),project]
  have high : d &&& 41 = 41 := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    have tab : ∀ i : Fin 30, (41 : BitVec 30).getLsbD i.val = true →
        ∃ r ∈ ([2,16,32] : List ℕ), off (rows.get i) = off r := by decide
    cases hv : (41 : BitVec 30).getLsbD j
    · rw [BitVec.getLsbD_and,hv,Bool.and_false]
    · obtain ⟨r,hr,eq⟩ := tab ⟨j,hj⟩ hv
      have gd := probe ⟨j,hj⟩
      change d.getLsbD j = (C.wires (List.ofFn (off (rows.get ⟨j,hj⟩)))).getD w false at gd
      rw [eq] at gd
      rw [BitVec.getLsbD_and,hv,gd,neighbors r hr]
      rfl

  have avoid (g : Gate) (hg : g ∈ pre) : 0 ∉ g.inputs := by
    obtain ⟨j,hj⟩ := List.mem_iff_getElem?.mp hg
    change (C.gates.take k)[j]? = _ at hj
    rw [List.getElem?_take] at hj
    split at hj
    · rename_i hjk
      apply sched.2.2 j g _ hj
      dsimp only [k] at hjk
      omega
    · contradiction
  have commutes (p : List (Bool × ℕ × ℕ)) (ws : List (BitVec 30)) (hn : 0 < ws.length)
      (clean : ∀ g ∈ p, g.2.1 ≠ 0 ∧ g.2.2 ≠ 0) :
      p.foldl put (ws.set 0 z) = (p.foldl put ws).set 0 z := by
    induction p generalizing ws with
    | nil => rfl
    | cons g p ih =>
      obtain ⟨ha,hb⟩ := clean g List.mem_cons_self
      have read (j : ℕ) (hj : j ≠ 0) : (ws.set 0 z).getD j 0 = ws.getD j 0 := by
        simp only [List.getD_eq_getElem?_getD,List.getElem?_set_ne (Ne.symm hj)]
      have st : put (ws.set 0 z) g = (put ws g).set 0 z := by
        dsimp only [put]
        rw [List.set_append_left _ _ hn,read _ ha,read _ hb]
      rw [List.foldl_cons,List.foldl_cons,st]
      exact ih _ (by simp [put]) (fun a h => clean a (List.mem_cons_of_mem _ h))
  have pref : A.foldl put (base.set 0 z) = W.set 0 z := by
    apply commutes _ _ (by decide)
    intro t ht
    obtain ⟨g,hg,rfl⟩ := List.mem_map.mp ht
    obtain ⟨a,b,ins⟩ := pair g (preMem g hg)
    have nz := avoid g hg
    simp only [ins,List.mem_cons,List.not_mem_nil,or_false,not_or] at nz
    exact ⟨by simpa [encode,ins] using Ne.symm nz.1, by simpa [encode,ins] using Ne.symm nz.2⟩
  have initial (i : Fin 30) : (base.set 0 z).map (bit i) = List.ofFn (changed (rows.get i)) := by
    have raw : ∀ i : Fin 30, (579928105 : BitVec 30).getLsbD i.val = (rows.get i).testBit 0 := by decide
    have replace : ∀ (i : Fin 30) (b : Bool), (List.ofFn (off (rows.get i))).set 0 b =
      List.ofFn (Function.update (row (rows.get i)) (0 : Fin 10) b) := by decide
    rw [List.map_set,offInputs,replace]
    have ht : bit i z = ((rows.get i).testBit 0 && guard (rows.get i)) := by
      exact (BitVec.getLsbD_and).trans (congrArg₂ Bool.and (raw i) (probe i))
    rw [ht]
  let bank := B.foldl put (W.set 0 z)
  have output : bank.getD C.output 0 = 32767 := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    let i : Fin 30 := ⟨j,hj⟩
    have sim := simulate C.gates (fun _ h => h) i (base.set 0 z)
    rw [initial,← concat,List.map_append,List.foldl_append] at sim
    change (B.foldl put (A.foldl put (base.set 0 z))).map (bit i) = _ at sim
    rw [pref,concat] at sim
    have bind : bit i (bank.getD C.output 0) = C.eval (List.ofFn (changed (rows.get i))) := by
      rw [← project]
      exact congrArg (fun t : List Bool => t.getD C.output false) sim
    have signs : ∀ ii : Fin 30,
        ((32767 : BitVec 30).getLsbD ii.val = true ∧ rows.get ii ∈ ([3,6,12,17,24,33,66,132,160,264,288,320,528,576,640] : List ℕ)) ∨
        ((32767 : BitVec 30).getLsbD ii.val = false ∧ rows.get ii ∈ ([50,69,104,116,138,201,208,276,385,402,521,548,554,770,773] : List ℕ)) := by decide
    change bit i _ = (32767 : BitVec 30).getLsbD i.val
    rw [bind]
    rcases signs i with ⟨h,hr⟩ | ⟨h,hr⟩
    · exact (tests.1 _ hr).trans h.symm
    · exact (tests.2 _ hr).trans h.symm
  have memOut : (32767 : BitVec 30) ∈ bank := by
    by_cases h : C.output < bank.length
    · rw [List.getD_eq_getElem _ _ h] at output
      exact output ▸ List.getElem_mem h
    · rw [List.getD_eq_default _ _ (by omega)] at output
      exact False.elim ((by decide : (0 : BitVec 30) ≠ 32767) output)
  let pool (s : List (BitVec 30)) := s.flatMap fun a => s.flatMap fun b => [a &&& b,a ||| b]
  have readMem (s : List (BitVec 30)) (j : ℕ) (h : (0 : BitVec 30) ∈ s) : s.getD j 0 ∈ s := by
    by_cases hj : j < s.length
    · rw [List.getD_eq_getElem _ _ hj]
      exact List.getElem_mem hj
    · rw [List.getD_eq_default _ _ (by omega)]
      exact h
  have generated (s : List (BitVec 30)) (g : Bool × ℕ × ℕ) (hs : (0 : BitVec 30) ∈ s) :
      ∃ v ∈ pool s, put s g = s ++ [v] := by
    refine ⟨_,?_,rfl⟩
    apply List.mem_flatMap.mpr
    refine ⟨_,readMem s g.2.1 hs,List.mem_flatMap.mpr ⟨_,readMem s g.2.2 hs,?_⟩⟩
    split <;> simp
  have checked (s : List (BitVec 30)) (f : BitVec 30 → Prop) [DecidablePred f]
      (ok : s.all (fun v => decide (f v)) = true) : ∀ v ∈ s, f v := by
    intro v hv
    exact of_decide_eq_true (List.all_eq_true.mp ok v hv)
  have orig : ∀ v ∈ base, v &&& 41 ≠ 41 := checked _ _ (by decide)
  have hasd : d ∈ W := by
    rw [show d = W[w] from List.getD_eq_getElem _ _ wBound]
    exact List.getElem_mem wBound
  have wEq : w = 9 + A.length := by
    by_contra h
    have hz : k = 0 := by dsimp only [k] at lenA ⊢; omega
    have ha : A = [] := List.length_eq_zero_iff.mp (lenA.trans hz)
    have eq : W = base := by change A.foldl put base = base; rw [ha]; rfl
    exact orig d (eq ▸ hasd) high
  have minGate : 2 ≤ A.length := by
    by_contra h
    obtain ⟨t,ht,hlen⟩ := growth base A
    change W = _ at ht
    rcases List.mem_append.mp (ht ▸ hasd) with old | new
    · exact orig _ old high
    · cases hA : A with
      | nil =>
        have he : t = [] := List.length_eq_zero_iff.mp (hlen.trans (congrArg List.length hA))
        exact List.not_mem_nil (he ▸ new)
      | cons g gs =>
        have tail : gs = [] := by apply List.length_eq_zero_iff.mp; rw [hA,List.length_cons] at h; omega
        have bankEq : W = put base g := by change A.foldl put base = _; rw [hA,tail]; rfl
        obtain ⟨v,hv,eq⟩ := generated base g (by decide)
        rcases List.mem_append.mp ((bankEq.trans eq) ▸ hasd) with old | one
        · exact orig _ old high
        · have none : ∀ v ∈ pool base, v &&& 41 ≠ 41 := checked _ _ (by decide)
          exact none v hv ((List.mem_singleton.mp one) ▸ high)
  by_cases short : A.length = 2
  · obtain ⟨g,h,hA⟩ : ∃ g h, A = [g,h] := by
      cases e : A with
      | nil => simp [e] at short
      | cons g gs =>
        cases gs with
        | nil => simp [e] at short
        | cons h hs =>
          have nil : hs = [] := by apply List.length_eq_zero_iff.mp; simpa [e] using short
          exact ⟨g,h,by rw [nil]⟩
    obtain ⟨p,hp,e₁⟩ := generated base g (by decide)
    obtain ⟨q,hq,e₂⟩ := generated (base ++ [p]) h (List.mem_append_left _ (by decide : (0 : BitVec 30) ∈ base))
    have eq : W = base ++ [p,q] := by
      change A.foldl put base = _
      rw [hA]; change put (put base g) h = _
      rw [e₁,e₂,List.append_assoc]; rfl
    have ed : d = q := by
      change W.getD w 0 = _
      rw [eq,wEq,short]
      rfl
    let good := fun (x y : BitVec 30) => y &&& 41 = 41 →
      x ∈ ([426545243,487490915,224826680] : List (BitVec 30)) ∧ y = 493786491
    let test := fun x => (pool (base ++ [x])).all (fun y => decide (good x y))
    have allGood : ((pool base).eraseDups.all test) = true := by decide
    have classify (x) (hx : x ∈ pool base) : ∀ y ∈ pool (base ++ [x]), good x y := by
      apply checked
      apply List.all_eq_true.mp allGood
      simpa using hx
    obtain ⟨hp',hq'⟩ := classify p hp q hq (ed ▸ high)
    have ez : z = 41 := by rw [show z = 579928105 &&& d from rfl,ed,hq']; rfl
    apply two p B hp' (by omega)
    change (32767 : BitVec 30) ∈ B.foldl put _
    change (32767 : BitVec 30) ∈ B.foldl put (W.set 0 z) at memOut
    rw [eq,ez,hq'] at memOut
    exact memOut
  have long : 3 ≤ A.length := by omega
  by_cases many : 2 ≤ B.length
  · apply late A B long many (by omega)
    · exact wEq ▸ high
    · exact wEq ▸ memOut
  let P := fun v : BitVec 30 => v.getLsbD 0 = true → v.getLsbD 15 = true
  have zeroP : P 0 := by decide
  have getP (s : List (BitVec 30)) (hs : ∀ v ∈ s, P v) (j : ℕ) : P (s.getD j 0) := by
    by_cases h : j < s.length
    · rw [List.getD_eq_getElem _ _ h]; exact hs _ (List.getElem_mem h)
    · rw [List.getD_eq_default _ _ (by omega)]; exact zeroP
  have closed (a b : BitVec 30) (pa : P a) (pb : P b) : P (a &&& b) ∧ P (a ||| b) := by
    dsimp only [P] at pa pb ⊢
    simp only [BitVec.getLsbD_and,BitVec.getLsbD_or,Bool.and_eq_true,Bool.or_eq_true]
    exact ⟨fun h => ⟨pa h.1,pb h.2⟩, fun h => h.imp pa pb⟩
  have allP (p : List (Bool × ℕ × ℕ)) (s : List (BitVec 30)) (hs : ∀ v ∈ s, P v) :
      ∀ v ∈ p.foldl put s, P v := by
    induction p generalizing s with
    | nil => exact hs
    | cons g p ih =>
      apply ih
      intro v hv
      rcases List.mem_append.mp hv with old | new
      · exact hs v old
      · obtain rfl := List.mem_singleton.mp new
        have h := closed _ _ (getP s hs g.2.1) (getP s hs g.2.2)
        split <;> first | exact h.2 | exact h.1
  have before : ∀ v ∈ W, P v := allP A base (by apply checked; decide)
  have notTarget : ¬P 32767 := by decide
  have zBit : z.getLsbD 1 = false := by
    change ((579928105 : BitVec 30) &&& d).getLsbD 1 = false
    rw [BitVec.getLsbD_and]; rfl
  have nzT : z ≠ 32767 := fun h => (by decide : (32767 : BitVec 30).getLsbD 1 ≠ false) (h ▸ zBit)
  have inSet (v) (hv : v ∈ W.set 0 z) : v = z ∨ v ∈ W := by
    cases eq : W with
    | nil => simp [eq] at hv
    | cons q qs =>
      simp only [eq,List.set_cons_zero,List.mem_cons] at hv ⊢
      exact hv.imp_right Or.inr
  have notYet : (32767 : BitVec 30) ∉ W.set 0 z := by
    intro h
    exact (inSet _ h).elim (fun he => nzT he.symm) (fun he => notTarget (before _ he))
  obtain ⟨g,hB⟩ : ∃ g, B = [g] := by
    cases e : B with
    | nil =>
      exact False.elim (notYet (by simpa only [bank,e,List.foldl_nil] using memOut))
    | cons g gs =>
      have eq : gs = [] := by apply List.length_eq_zero_iff.mp; rw [e,List.length_cons] at many; omega
      exact ⟨g,by rw [eq]⟩
  have final : put (W.set 0 z) g = bank := by simp only [bank,hB,List.foldl_cons,List.foldl_nil]
  rw [← final] at memOut
  have eqFinal := List.mem_singleton.mp ((List.mem_append.mp memOut).resolve_left notYet)
  let rd := fun j => (W.set 0 z).getD j 0
  have casesRead (j) : rd j = z ∨ rd j ∈ W := by
    by_cases h : j < (W.set 0 z).length
    · apply inSet; rw [show rd j = (W.set 0 z)[j] from List.getD_eq_getElem _ _ h]
      exact List.getElem_mem h
    · right
      have hz : rd j = 0 := List.getD_eq_default _ _ (by omega)
      obtain ⟨t,ht,_⟩ := growth base A
      change W = _ at ht
      rw [hz,ht]
      exact List.mem_append_left _ (by decide)
  have orGate : ∃ v ∈ W, z ||| v = 32767 := by
    change (32767 : BitVec 30) = (if g.1 then rd g.2.1 ||| rd g.2.2 else rd g.2.1 &&& rd g.2.2) at eqFinal
    rcases casesRead g.2.1 with a | a <;> rcases casesRead g.2.2 with b | b
    · rw [a,b] at eqFinal
      split at eqFinal <;> simp only [BitVec.or_self,BitVec.and_self] at eqFinal <;> exact (nzT eqFinal.symm).elim
    · rw [a] at eqFinal
      split at eqFinal
      · exact ⟨_,b,eqFinal.symm⟩
      · have h := congrArg (fun x : BitVec 30 => x.getLsbD 1) eqFinal
        change true = (z &&& rd g.2.2).getLsbD 1 at h
        rw [BitVec.getLsbD_and,zBit] at h
        contradiction
    · rw [b] at eqFinal
      split at eqFinal
      · exact ⟨_,a,(BitVec.or_comm ..).trans eqFinal.symm⟩
      · have h := congrArg (fun x : BitVec 30 => x.getLsbD 1) eqFinal
        change true = (rd g.2.1 &&& z).getLsbD 1 at h
        rw [BitVec.getLsbD_and,zBit,Bool.and_false] at h
        contradiction
    · have h := closed _ _ (before _ a) (before _ b)
      apply False.elim
      apply notTarget
      rw [eqFinal]
      split <;> first | exact h.2 | exact h.1
  obtain ⟨v,hv,hit⟩ := orGate
  have ez : z = 41 := by
    calc
      z = z &&& (z ||| v) := by
        generalize z = x
        apply BitVec.eq_of_getLsbD_eq
        intro j hj
        rw [BitVec.getLsbD_and,BitVec.getLsbD_or]
        cases x.getLsbD j <;> rfl
      _ = z &&& 32767 := by rw [hit]
      _ = d &&& ((579928105 : BitVec 30) &&& 32767) := by dsimp only [z]; ac_rfl
      _ = 41 := high
  have lB : B.length = 1 := by rw [hB]; rfl
  apply last A (by omega) (wEq ▸ high) (wEq ▸ ez) v hv
  exact ez ▸ hit
