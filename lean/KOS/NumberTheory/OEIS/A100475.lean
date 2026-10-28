import Mathlib

/-
The definitions `reverseDigits`, `a`, `aStartAt` and `IsUltimatelyPeriodic` below are copied
verbatim from `FormalConjectures/OEIS/100475.lean` of google-deepmind/formal-conjectures
(Copyright 2026 The Formal Conjectures Authors, Apache License 2.0), omitting only the
repository-specific attributes.  `OeisA100475.conjecture` there is the open statement
`∃ x : ℕ, 0 < x ∧ x ≠ 1 ∧ IsUltimatelyPeriodic (aStartAt x)`.
-/

namespace OeisA100475

/-- Reverses the base 10 digits of a natural number. -/
def reverseDigits (k : ℕ) : ℕ :=
  Nat.ofDigits 10 (Nat.digits 10 k |>.reverse)

/-- The primary defining sequence `a`.
a n is the Prime-th recurrence with reversal at each step.
$a(n) = \operatorname{reversal}(p_{a(n-1)})$
with $a(0)=1$, where $p_k$ is the $k$-th prime number (i.e., $p_1=2, p_2=3, \dots$). -/
noncomputable def a : ℕ → ℕ
  | 0 => 1
  | n + 1 =>
    let k := a n
    if k = 0 then 0
    else reverseDigits (Nat.nth Nat.Prime (k - 1))

/-- Definition of the generalized sequence starting at x. -/
noncomputable def aStartAt (x : ℕ) : ℕ → ℕ
  | 0 => x
  | n + 1 =>
    let k := aStartAt x n
    if k = 0 then 0
    else reverseDigits (Nat.nth Nat.Prime (k - 1))

/-- A sequence $f : \mathbb{N} \to \mathbb{N}$ is ultimately periodic if there exist
$N, P \in \mathbb{N}$, with $P>0$, such that for all $n \ge N$, $f(n+P) = f(n)$. -/
def IsUltimatelyPeriodic (f : ℕ → ℕ) : Prop :=
  ∃ N P, P > 0 ∧ ∀ n, n ≥ N → f (n + P) = f n

end OeisA100475


/-!
# OEIS A100475: no positive start value leads to a loop

We prove `OeisA100475.not_conjecture`, i.e. a *negative* answer to the open question
`OeisA100475.conjecture`: for every `x > 0` the sequence `aStartAt x`
(`a(n+1) = rev(p_{a(n)})`, `p_k` the `k`-th prime, `p_1 = 2`) is not ultimately periodic.

## Proof outline

Let `F k = rev (p_k)` with `p_k = nth Nat.Prime (k - 1)`, and let `numDigits n` be the number of
decimal digits of `n`.

1. `F k ≠ 0`, so an orbit started at `x > 0` stays positive and
   `aStartAt x (n + 1) = F (aStartAt x n)`.
2. `p_k ≥ k + 1` and no prime ends in the digit `0`, so `numDigits k ≤ numDigits (F k)`:
   the digit count is non-decreasing along every orbit.
3. On a periodic tail the digit count is therefore constant, so every tail element `k` satisfies
   `numDigits (F k) = numDigits k = d`, whence `10^(d-1) ≤ k ≤ π'(10^d)`.
4. `π'(10^d) < 10^(d-1)` for every `d ≥ 5` (`count_pow_ten`): for `d = 5, 6, 7` by Legendre's
   sieve with the first 60 primes, evaluated by the kernel, and for `d ≥ 8` by induction using
   Chebyshev's elementary bound `primorial n ≤ 4^n`.  Hence `d ≤ 4` and `k ≤ π'(10^4) = 1229`.
5. A kernel computation shows that every orbit starting in `[1, 1229]` leaves `[1, 1229]` within
   10 steps (`escapes`), which contradicts 3–4.

All finite computations are checked by the kernel via `decide +kernel` (no `native_decide`).
The kernel-evaluated functions are written with explicit `Nat.rec`/`List.rec` and Boolean
primitives so that the kernel's GMP-accelerated `Nat` operations do the work.
-/

namespace OeisA100475

/- ### Decimal digits and the step map -/

/-- Number of decimal digits. -/
def numDigits (n : ℕ) : ℕ := (Nat.digits 10 n).length

/-- Reversal of a number not ending in `0` reverses its digit list. -/
theorem digits_reverseDigits {n : ℕ} (h : n % 10 ≠ 0) :
    Nat.digits 10 (reverseDigits n) = (Nat.digits 10 n).reverse := by
  have hn : 0 < n := Nat.pos_of_ne_zero (by rintro rfl; simp at h)
  have hd : Nat.digits 10 n = (n % 10) :: Nat.digits 10 (n / 10) :=
    Nat.digits_def' (by norm_num) hn
  unfold reverseDigits
  apply Nat.digits_ofDigits 10 (by norm_num)
  · intro l hl
    rw [List.mem_reverse] at hl
    exact Nat.digits_lt_base (by norm_num) hl
  · intro hne
    rw [List.getLast_reverse]
    simp only [hd, List.head_cons]
    exact h

/-- No prime ends in the digit `0`. -/
theorem prime_mod_ten_ne_zero {p : ℕ} (hp : p.Prime) : p % 10 ≠ 0 := by
  intro h
  have h10 : 10 ∣ p := Nat.dvd_of_mod_eq_zero h
  have h2 : 2 ∣ p := dvd_trans (by norm_num) h10
  have h5 : 5 ∣ p := dvd_trans (by norm_num) h10
  rcases hp.eq_one_or_self_of_dvd 2 h2 with h | h <;>
    rcases hp.eq_one_or_self_of_dvd 5 h5 with h' | h' <;> omega

theorem numDigits_reverseDigits_prime {p : ℕ} (hp : p.Prime) :
    numDigits (reverseDigits p) = numDigits p := by
  unfold numDigits
  rw [digits_reverseDigits (prime_mod_ten_ne_zero hp), List.length_reverse]

theorem reverseDigits_prime_ne_zero {p : ℕ} (hp : p.Prime) : reverseDigits p ≠ 0 := by
  intro h
  have h1 := numDigits_reverseDigits_prime hp
  rw [h] at h1
  have h2 : numDigits p ≠ 0 := by
    unfold numDigits
    rw [Ne, List.length_eq_zero_iff, Nat.digits_eq_nil_iff_eq_zero]
    exact hp.ne_zero
  simp [numDigits] at h1
  exact h2 h1.symm

/-- The step map `k ↦ rev(p_k)`. -/
noncomputable def F (k : ℕ) : ℕ := reverseDigits (Nat.nth Nat.Prime (k - 1))

theorem F_ne_zero (k : ℕ) : F k ≠ 0 :=
  reverseDigits_prime_ne_zero (Nat.prime_nth_prime _)

theorem aStartAt_succ (x n : ℕ) :
    aStartAt x (n + 1) = if aStartAt x n = 0 then 0 else F (aStartAt x n) := rfl

theorem aStartAt_ne_zero {x : ℕ} (hx : 0 < x) (n : ℕ) : aStartAt x n ≠ 0 := by
  induction n with
  | zero => exact hx.ne'
  | succ n ih => rw [aStartAt_succ, if_neg ih]; exact F_ne_zero _

theorem aStartAt_succ' {x : ℕ} (hx : 0 < x) (n : ℕ) :
    aStartAt x (n + 1) = F (aStartAt x n) := by
  rw [aStartAt_succ, if_neg (aStartAt_ne_zero hx n)]

theorem numDigits_F (k : ℕ) : numDigits (F k) = numDigits (Nat.nth Nat.Prime (k - 1)) :=
  numDigits_reverseDigits_prime (Nat.prime_nth_prime _)

/-- The digit count never decreases along an orbit, since `p_k > k`. -/
theorem numDigits_le_F {k : ℕ} (hk : 1 ≤ k) : numDigits k ≤ numDigits (F k) := by
  rw [numDigits_F]
  apply Nat.le_length_digits_le
  have := Nat.add_two_le_nth_prime (k - 1)
  omega

theorem aStartAt_add {x : ℕ} (hx : 0 < x) (N j : ℕ) :
    aStartAt x (N + j) = F^[j] (aStartAt x N) := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [← Nat.add_assoc, aStartAt_succ' hx, ih, Function.iterate_succ_apply']

/- ### Kernel-checked computations: primes below `10^4` and the escape check -/

/-- `trialDiv n f d` checks that no `m ∈ [d, d + f)` with `m * m ≤ n` divides `n`. -/
noncomputable def trialDiv (n : ℕ) (f : ℕ) : ℕ → Bool :=
  Nat.rec (motive := fun _ => ℕ → Bool) (fun _ => true)
    (fun _ ih d => cond (Nat.blt n (d * d)) true (cond (Nat.beq (n % d) 0) false (ih (d + 1)))) f

theorem trialDiv_zero (n d : ℕ) : trialDiv n 0 d = true := rfl

theorem trialDiv_succ (n f d : ℕ) : trialDiv n (f + 1) d =
    cond (Nat.blt n (d * d)) true (cond (Nat.beq (n % d) 0) false (trialDiv n f (d + 1))) := rfl

/-- Specification of `trialDiv`. -/
theorem trialDiv_iff (n f d : ℕ) :
    trialDiv n f d = true ↔ ∀ m, d ≤ m → m < d + f → m * m ≤ n → n % m ≠ 0 := by
  induction f generalizing d with
  | zero =>
    rw [trialDiv_zero]
    simp only [true_iff]
    intro m h1 h2
    omega
  | succ f ih =>
    rw [trialDiv_succ]
    simp only [Bool.cond_eq_ite, Nat.blt_eq, Nat.beq_eq]
    split_ifs with h1 h2
    · simp only [true_iff]
      intro m hm _ hmm
      have : d * d ≤ m * m := Nat.mul_le_mul hm hm
      omega
    · simp only [false_iff, not_forall]
      exact ⟨d, le_refl d, by omega, by omega, by simpa using h2⟩
    · rw [ih]
      constructor
      · intro H m hm1 hm2 hm3
        rcases Nat.eq_or_lt_of_le hm1 with rfl | hlt
        · exact h2
        · exact H m hlt (by omega) hm3
      · intro H m hm1 hm2 hm3
        exact H m (by omega) (by omega) hm3

/-- Boolean primality test by trial division. -/
noncomputable def isPrimeB (n : ℕ) : Bool := Nat.blt 1 n && trialDiv n n 2

theorem isPrimeB_iff (n : ℕ) : isPrimeB n = true ↔ n.Prime := by
  unfold isPrimeB
  rw [Bool.and_eq_true, Nat.blt_eq, trialDiv_iff]
  constructor
  · rintro ⟨h1, h2⟩
    by_contra hnp
    have hsq := Nat.minFac_sq_le_self (by omega : 0 < n) hnp
    have hmp : (Nat.minFac n).Prime := Nat.minFac_prime (by omega)
    have h2le := hmp.two_le
    have hdvd := Nat.minFac_dvd n
    have hle : Nat.minFac n ≤ n := Nat.minFac_le (by omega)
    exact h2 (Nat.minFac n) h2le (by omega) (by rw [← pow_two]; exact hsq)
      (Nat.mod_eq_zero_of_dvd hdvd)
  · intro hp
    refine ⟨hp.one_lt, fun m hm1 _ hm3 hm4 => ?_⟩
    have hdvd : m ∣ n := Nat.dvd_of_mod_eq_zero hm4
    rcases hp.eq_one_or_self_of_dvd m hdvd with h | h
    · omega
    · subst h
      have := hp.two_le
      have : m * 2 ≤ m * m := Nat.mul_le_mul_left m hm1
      omega

/-- The first 1229 primes (those below `10^4`), packed in 14-bit fields. -/
def PT : ℕ := 20255257391043842915494497417660758049176729481909770637864941242945698380333077098019055476408443946374250391334314018578570363222215396608970470537980326347903438933100108140964564403265882033429108259737351958956723170298128303912551534528048165510713519865542188669229592559146286719132711235525078592157864113488547747251216796037687173240232372321719447463193146772455434579499807402503491962901738411997631350433584313204499331768868949510745335747105768812134191118924246309803197016347673242771601514276227089518724324241149805739197300348033026364239587699117414462987278661001227594497258338561231074737085192510451343898611952938821244273570577320928394568892462353663646862338220062588318801953506936369870779119272273287024230184617839758354298464837645145468756602812307410215133728470615770239984090744851418231590346918652816612172060918455234850311196019753939825645378849080355696908918299740587734371819057002793531186554349616342471167018768357895890495435899725344279202034515543385985732239082387497359223253033173886287523764929304169426021622663980448272753840478874921664378712265057713046749749166565623778515946742087890092057054369557495190778587195679453775200036137041311406920152630238735338413819617149911111155409917829714693568177709861618074254397014904074739765885129987042008649086797118504530570324765873968996801575325254069884612826212588625080419576256061533729873938274356816128842197045907759053024697616610098609913968551012015604301681347148683546499996108594026891393044060869943037219708800524710922458571049178417633048834628468599833534160742639209673019215752310511290004219596318190722102453566551573826170301485211501678390188564633259990031733173213229968817658699970870814819989359457619975591069042634401501311443881040091582252288967511315629688381066942526183013087825204056045765686431699312888101371260585616744477050935907875691248424831675097085982394388840489393889916522284953423429196375586432858679203337675408368011876783096182926168584984735602112235413573226701103583018747961508856589056184444934597224149298396054180335154348363300688471236465894526449275320570055434832283991523124764476605383420053591348349359234991446570751565565333668174460310658071916536781657736617368049530279789182495984033432678162546795566259605569133087756287563945632137666126054122636121796856546965338836464402136318355288096830709223076182950097330398807173506665455045043956955975056640918012718965574225138450584002647901559425619325616142138441422188800575708224547872067477190962169177389460632587342048982361775667126745845651675365419002435427000285594496577252353086946815401310908322698309082798944265005061162541115466619335388901126568095300039383556988687445261309109959614143720010858869809100019830393403590649692329850119106658450442815176889827485768284846981473226213434524680071236023540919338884108354753012019493808568397209275891759064038642125422449469479572431827808604802027934295699422502597487566312670013851430497473778709403987675904011895279869671012432811803066889547807694947613015839309668309773505171279018466686745387986081980920573002242908548869406312103422176972629122387937964109484643050433837411170421958287130223536641936774633377918800056386360322525888986078677135250512982982555140098960746547015785751324996706891199836945021855641180140129186024977342556132633197742251472453711608655333037168293191939312861458982038570172039506533269839878350887592571897735732878375417361822932483153098897619479275884462557854195367291790684054596120796609816944806715439662069683198667787526551571549751143177697338868655903441782571286075640503990603412306490641328275154481737895001803713318998711119727809536586699021229061739022239829323848674368773978904473360759508082443020506779391827762733840558655723921891885473580113335462526876059649009382543197924827070692530556515219490661398428325417966617266368902629628429116087766804570550754200733232365843539921984777467892573415512463916812299596420758598705329709421217197151217520351695175497272985357990731296463952273685583643247023963808577511041092273372820836691650087217840108121369052659486254548126806336189250785038035573017247589637782815119463693333622921422653272549184944335888536296102765193609621261672618509643280468525847172507683302958408769631656877541985410739059294281546793451678358816769808758803796745744180592857830298425317868191869071647926237355107748604540002617666397260559368749385387182112343387175378499774567667898077070735835830673282967137483748530598773828692217590925289295616371028248957265399846252631089692653866533544356647054715553008475172272453877801252754440093058459943984176855361084678229461838505810428041606399154542650033831369034162010434815089114633184389665928960146541108059611125637716744992536507357071221922239995223564786336247161611605789347846151002501459477104831686414943016096466872114785063819231959002662325203458274198483256449289535711930665012904339141346938625826751886094202526768031289860071287686863275456511120425982566367987631060051640606403747964930136367765282219729965581584859063050258465212156551572006295279251648365114075806584418107947968230947078146

/-- `Ptab i` is the `i`-th field of `PT`. -/
def Ptab (i : ℕ) : ℕ := Nat.shiftRight PT (14 * i) % 16384

/-- Walk through `n, n+1, …` keeping `c = π'(n)` and checking primes against the table. -/
noncomputable def walk (f : ℕ) : ℕ → ℕ → Bool :=
  Nat.rec (motive := fun _ => ℕ → ℕ → Bool) (fun _ c => Nat.beq c 1229)
    (fun _ ih n c => cond (isPrimeB n) (Nat.beq (Ptab c) n && ih (n + 1) (c + 1))
      (ih (n + 1) c)) f

theorem walk_zero (n c : ℕ) : walk 0 n c = Nat.beq c 1229 := rfl

theorem walk_succ (f n c : ℕ) : walk (f + 1) n c =
    cond (isPrimeB n) (Nat.beq (Ptab c) n && walk f (n + 1) (c + 1)) (walk f (n + 1) c) := rfl

/-- Soundness of `walk`: it certifies `π'(10^4) = 1229` and the table `Ptab`. -/
theorem walk_sound (f : ℕ) : ∀ n c, walk f n c = true → c = Nat.count Nat.Prime n →
    (∀ i < c, Nat.nth Nat.Prime i = Ptab i) →
    Nat.count Nat.Prime (n + f) = 1229 ∧ ∀ i < 1229, Nat.nth Nat.Prime i = Ptab i := by
  induction f with
  | zero =>
    intro n c hw hc hi
    rw [walk_zero, Nat.beq_eq] at hw
    subst hw
    exact ⟨hc.symm, hi⟩
  | succ f ih =>
    intro n c hw hc hi
    rw [walk_succ] at hw
    rw [show n + (f + 1) = n + 1 + f by omega]
    cases hp : isPrimeB n
    · rw [hp, cond_false] at hw
      have hnp : ¬ n.Prime := by rw [← isPrimeB_iff, hp]; simp
      exact ih (n + 1) c hw (by rw [Nat.count_succ, if_neg hnp, hc, Nat.add_zero]) hi
    · rw [hp, cond_true, Bool.and_eq_true, Nat.beq_eq] at hw
      have hpr : n.Prime := (isPrimeB_iff n).mp hp
      refine ih (n + 1) (c + 1) hw.2 (by rw [Nat.count_succ, if_pos hpr, hc]) ?_
      intro i hi'
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi' with h | h
      · exact hi i h
      · rw [h, hw.1, hc, Nat.nth_count hpr]

set_option maxRecDepth 100000 in
theorem walk_ok : walk 10000 0 0 = true := by decide +kernel

/-- `π'(10^4) = 1229`, and `Ptab i` is the `(i+1)`-st prime for `i < 1229`. -/
theorem table_facts :
    Nat.count Nat.Prime 10000 = 1229 ∧ ∀ i < 1229, Nat.nth Nat.Prime i = Ptab i := by
  have := walk_sound 10000 0 0 walk_ok (by simp) (by simp)
  simpa using this

/-- Digit reversal with fuel, accumulator style. -/
noncomputable def revAux (f : ℕ) : ℕ → ℕ → ℕ :=
  Nat.rec (motive := fun _ => ℕ → ℕ → ℕ) (fun _ acc => acc)
    (fun _ ih n acc => cond (Nat.beq n 0) acc (ih (n / 10) (acc * 10 + n % 10))) f

theorem revAux_zero (n acc : ℕ) : revAux 0 n acc = acc := rfl

theorem revAux_succ (f n acc : ℕ) : revAux (f + 1) n acc =
    cond (Nat.beq n 0) acc (revAux f (n / 10) (acc * 10 + n % 10)) := rfl

theorem reverseDigits_zero : reverseDigits 0 = 0 := by simp [reverseDigits]

/-- `revAux` computes `reverseDigits` once the fuel covers all digits. -/
theorem revAux_spec (f : ℕ) : ∀ n acc, numDigits n ≤ f →
    revAux f n acc = acc * 10 ^ numDigits n + reverseDigits n := by
  induction f with
  | zero =>
    intro n acc h
    have hn : n = 0 := by
      have : numDigits n = 0 := by omega
      unfold numDigits at this
      rwa [List.length_eq_zero_iff, Nat.digits_eq_nil_iff_eq_zero] at this
    subst hn
    simp [revAux_zero, numDigits, reverseDigits_zero]
  | succ f ih =>
    intro n acc h
    rw [revAux_succ]
    simp only [Bool.cond_eq_ite, Nat.beq_eq]
    split_ifs with hn
    · subst hn
      simp [numDigits, reverseDigits_zero]
    · have hd : Nat.digits 10 n = (n % 10) :: Nat.digits 10 (n / 10) :=
        Nat.digits_def' (by norm_num) (Nat.pos_of_ne_zero hn)
      have hnd : numDigits n = numDigits (n / 10) + 1 := by
        unfold numDigits; rw [hd, List.length_cons]
      rw [ih (n / 10) _ (by omega), hnd]
      have hrev : reverseDigits n = reverseDigits (n / 10) + 10 ^ numDigits (n / 10) * (n % 10) := by
        unfold reverseDigits numDigits
        rw [hd, List.reverse_cons, Nat.ofDigits_append, List.length_reverse, Nat.ofDigits_singleton]
      rw [hrev, pow_succ]
      ring

/-- Computable version of `F` on `[1, 1229]`. -/
noncomputable def G (k : ℕ) : ℕ := revAux 5 (Ptab (k - 1)) 0

theorem G_eq_F {k : ℕ} (hk1 : 1 ≤ k) (hk2 : k ≤ 1229) : G k = F k := by
  unfold G F
  have hlt : Ptab (k - 1) < 16384 := Nat.mod_lt _ (by norm_num)
  rw [revAux_spec 5 _ 0 ?_, zero_mul, zero_add, table_facts.2 (k - 1) (by omega)]
  unfold numDigits
  rw [Nat.digits_length_le_iff (by norm_num)]
  omega

/-- `escape f k`: the orbit of `k` exceeds 1229 within `f` steps (computed with `G`). -/
noncomputable def escape (f : ℕ) : ℕ → Bool :=
  Nat.rec (motive := fun _ => ℕ → Bool) (fun _ => false)
    (fun _ ih k => cond (Nat.blt 1229 k) true (ih (G k))) f

theorem escape_sound (f : ℕ) : ∀ k, 1 ≤ k → escape f k = true → ∃ j, 1229 < F^[j] k := by
  induction f with
  | zero => intro k _ h; exact absurd h (by simp [escape])
  | succ f ih =>
    intro k hk h
    change cond (Nat.blt 1229 k) true (escape f (G k)) = true at h
    simp only [Bool.cond_eq_ite, Nat.blt_eq] at h
    split_ifs at h with hlt
    · exact ⟨0, hlt⟩
    · rw [G_eq_F hk (by omega)] at h
      obtain ⟨j, hj⟩ := ih (F k) (Nat.one_le_iff_ne_zero.mpr (F_ne_zero k)) h
      exact ⟨j + 1, by rwa [Function.iterate_succ_apply]⟩

/-- Check `escape 10 k` for all `k ∈ [1, m]`. -/
noncomputable def allEsc (m : ℕ) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun k ih => ih && escape 10 (k + 1)) m

theorem allEsc_sound (m : ℕ) (h : allEsc m = true) :
    ∀ k, 1 ≤ k → k ≤ m → escape 10 k = true := by
  induction m with
  | zero => intro k h1 h2; omega
  | succ m ih =>
    change (allEsc m && escape 10 (m + 1)) = true at h
    rw [Bool.and_eq_true] at h
    intro k h1 h2
    rcases Nat.lt_or_ge k (m + 1) with hlt | hge
    · exact ih h.1 k h1 (by omega)
    · have : k = m + 1 := by omega
      subst this
      exact h.2

set_option maxRecDepth 100000 in
theorem allEsc_ok : allEsc 1229 = true := by decide +kernel

/-- Every orbit starting in `[1, 1229]` eventually exceeds `1229`. -/
theorem escapes {k : ℕ} (hk1 : 1 ≤ k) (hk2 : k ≤ 1229) : ∃ j, 1229 < F^[j] k :=
  escape_sound 10 k hk1 (allEsc_sound 1229 allEsc_ok k hk1 hk2)

/- ### Legendre's sieve: an upper bound for `π'(x)` -/

/-- `cpc l x = #{m ∈ [1, x] | ∀ q ∈ l, ¬ q ∣ m}`. -/
noncomputable def cpc (l : List ℕ) (x : ℕ) : ℕ :=
  Nat.count (fun n => ∀ q ∈ l, ¬ q ∣ n + 1) x

theorem cpc_zero (l : List ℕ) : cpc l 0 = 0 := Nat.count_zero _

theorem cpc_succ (l : List ℕ) (x : ℕ) :
    cpc l (x + 1) = cpc l x + if (∀ q ∈ l, ¬ q ∣ x + 1) then 1 else 0 :=
  Nat.count_succ _ _

theorem dvd_mul_iff_of_prime {r q m : ℕ} (hr : r.Prime) (hq : q.Prime) (hrq : r ≠ q) :
    r ∣ q * m ↔ r ∣ m := by
  constructor
  · intro h
    rcases (Nat.Prime.dvd_mul hr).mp h with h1 | h1
    · exact absurd ((Nat.prime_dvd_prime_iff_eq hr hq).mp h1) hrq
    · exact h1
  · exact fun h => dvd_mul_of_dvd_right h q

/-- Legendre's identity `φ(x, l) = φ(x, q :: l) + φ(x / q, l)`. -/
theorem cpc_split {q : ℕ} {l : List ℕ} (hq : q.Prime) (hl : ∀ r ∈ l, r.Prime) (hql : q ∉ l)
    (x : ℕ) : cpc l x = cpc (q :: l) x + cpc l (x / q) := by
  induction x with
  | zero => simp [cpc_zero]
  | succ x ih =>
    rw [cpc_succ, cpc_succ]
    by_cases hdvd : q ∣ x + 1
    · have e : (x + 1) / q = x / q + 1 := Nat.succ_div_of_dvd hdvd
      rw [e, cpc_succ]
      have hx : x + 1 = q * (x / q + 1) := by rw [← e]; exact (Nat.mul_div_cancel' hdvd).symm
      have key : (∀ r ∈ l, ¬ r ∣ x + 1) ↔ (∀ r ∈ l, ¬ r ∣ x / q + 1) := by
        constructor
        · intro h r hr hr'
          exact h r hr (by rw [hx]; exact dvd_mul_of_dvd_right hr' q)
        · intro h r hr hr'
          rw [hx] at hr'
          have hrq : r ≠ q := fun e => hql (e ▸ hr)
          exact h r hr ((dvd_mul_iff_of_prime (hl r hr) hq hrq).mp hr')
      have h2 : ¬ (∀ r ∈ q :: l, ¬ r ∣ x + 1) := fun h => h q List.mem_cons_self hdvd
      rw [if_neg h2]
      by_cases h3 : ∀ r ∈ l, ¬ r ∣ x + 1
      · rw [if_pos h3, if_pos (key.mp h3)]; omega
      · rw [if_neg h3, if_neg (fun h => h3 (key.mpr h))]; omega
    · rw [Nat.succ_div_of_not_dvd hdvd]
      have key : (∀ r ∈ q :: l, ¬ r ∣ x + 1) ↔ (∀ r ∈ l, ¬ r ∣ x + 1) := by
        simp only [List.mem_cons, forall_eq_or_imp]
        exact ⟨fun h => h.2, fun h => ⟨hdvd, h⟩⟩
      by_cases h3 : ∀ r ∈ l, ¬ r ∣ x + 1
      · rw [if_pos h3, if_pos (key.mpr h3)]; omega
      · rw [if_neg h3, if_neg (fun h => h3 (key.mp h))]; omega

/-- Kernel-friendly Legendre recursion; arguments are forced through `Nat.rec` so that the
kernel's `whnf` cache memoizes repeated subproblems. -/
noncomputable def phiS (l : List ℕ) : ℕ → ℕ :=
  List.rec (motive := fun _ => ℕ → ℕ) (fun x => x) (fun q _ ih x =>
    Nat.rec (motive := fun _ => ℕ) 0 (fun k _ => cond (Nat.blt (Nat.succ k) q) (ih (Nat.succ k))
      (Nat.sub (ih (Nat.succ k)) (ih (Nat.div (Nat.succ k) q)))) x) l

theorem phiS_nil (x : ℕ) : phiS [] x = x := rfl

theorem phiS_cons_zero (q : ℕ) (l : List ℕ) : phiS (q :: l) 0 = 0 := rfl

theorem phiS_cons_succ (q : ℕ) (l : List ℕ) (k : ℕ) : phiS (q :: l) (k + 1) =
    cond (Nat.blt (k + 1) q) (phiS l (k + 1)) (phiS l (k + 1) - phiS l ((k + 1) / q)) := rfl

/-- `phiS` computes the Legendre count `cpc` for a list of distinct primes. -/
theorem phiS_eq (l : List ℕ) (hl : ∀ r ∈ l, r.Prime) (hnd : l.Nodup) (x : ℕ) :
    phiS l x = cpc l x := by
  induction l generalizing x with
  | nil =>
    rw [phiS_nil]
    unfold cpc
    simp
  | cons q l ih =>
    have hq := hl q List.mem_cons_self
    have hl' : ∀ r ∈ l, r.Prime := fun r hr => hl r (List.mem_cons_of_mem q hr)
    have hnd' := List.nodup_cons.mp hnd
    have hsplit := cpc_split hq hl' hnd'.1 x
    cases x with
    | zero => rw [phiS_cons_zero, cpc_zero]
    | succ k =>
      rw [phiS_cons_succ, ih hl' hnd'.2, ih hl' hnd'.2]
      simp only [Bool.cond_eq_ite, Nat.blt_eq]
      split_ifs with hlt
      · rw [Nat.div_eq_of_lt hlt, cpc_zero] at hsplit
        omega
      · omega

/-- `π(x) ≤ |l| + φ(x, l)`: a prime `≤ x` lies in `l` or is coprime to all of `l`. -/
theorem count_prime_le (l : List ℕ) (hl : ∀ r ∈ l, r.Prime) (x : ℕ) :
    Nat.count Nat.Prime (x + 1) ≤ l.length + cpc l x := by
  unfold cpc
  rw [Nat.count_eq_card_filter_range, Nat.count_eq_card_filter_range]
  calc (Finset.filter Nat.Prime (Finset.range (x + 1))).card
      ≤ (l.toFinset ∪ (Finset.filter (fun n => ∀ q ∈ l, ¬ q ∣ n + 1)
          (Finset.range x)).image (· + 1)).card := by
        apply Finset.card_le_card
        intro p hp
        rw [Finset.mem_filter, Finset.mem_range] at hp
        rw [Finset.mem_union, List.mem_toFinset, Finset.mem_image]
        by_cases hpl : p ∈ l
        · exact Or.inl hpl
        · right
          have h2 := hp.2.two_le
          refine ⟨p - 1, ?_, by omega⟩
          rw [Finset.mem_filter, Finset.mem_range]
          refine ⟨by omega, ?_⟩
          rw [Nat.sub_add_cancel (by omega)]
          intro q hq hqp
          have := (Nat.prime_dvd_prime_iff_eq (hl q hq) hp.2).mp hqp
          exact hpl (this ▸ hq)
    _ ≤ l.toFinset.card + ((Finset.filter (fun n => ∀ q ∈ l, ¬ q ∣ n + 1)
          (Finset.range x)).image (· + 1)).card := Finset.card_union_le _ _
    _ ≤ l.length + (Finset.filter (fun n => ∀ q ∈ l, ¬ q ∣ n + 1) (Finset.range x)).card :=
        Nat.add_le_add (List.toFinset_card_le l) Finset.card_image_le

/-- The first 60 primes, in decreasing order. -/
def P60 : List ℕ := [281, 277, 271, 269, 263, 257, 251, 241, 239, 233, 229, 227, 223, 211, 199, 197, 193, 191, 181, 179, 173, 167, 163, 157, 151, 149, 139, 137, 131, 127, 113, 109, 107, 103, 101, 97, 89, 83, 79, 73, 71, 67, 61, 59, 53, 47, 43, 41, 37, 31, 29, 23, 19, 17, 13, 11, 7, 5, 3, 2]

theorem P60_prime : ∀ r ∈ P60, r.Prime := by
  have h : P60.all isPrimeB = true := by decide +kernel
  intro r hr
  rw [List.all_eq_true] at h
  exact (isPrimeB_iff r).mp (h r hr)

theorem P60_nodup : P60.Nodup := by decide +kernel

theorem count_prime_le_P60 (x : ℕ) : Nat.count Nat.Prime (x + 1) ≤ 60 + phiS P60 x := by
  have h := count_prime_le P60 P60_prime x
  rw [← phiS_eq P60 P60_prime P60_nodup] at h
  exact h

set_option maxRecDepth 100000 in
theorem phi5 : phiS P60 99999 = 9560 := by decide +kernel

set_option maxRecDepth 100000 in
theorem phi6 : phiS P60 999999 = 95648 := by decide +kernel

set_option maxRecDepth 100000 in
theorem phi7 : phiS P60 9999999 = 985311 := by decide +kernel

theorem count_le_5 : Nat.count Nat.Prime (10 ^ 5) < 10 ^ 4 := by
  have h := count_prime_le_P60 99999
  rw [phi5] at h
  norm_num at h ⊢
  omega

theorem count_le_6 : Nat.count Nat.Prime (10 ^ 6) < 10 ^ 5 := by
  have h := count_prime_le_P60 999999
  rw [phi6] at h
  norm_num at h ⊢
  omega

theorem count_le_7 : Nat.count Nat.Prime (10 ^ 7) < 10 ^ 6 := by
  have h := count_prime_le_P60 9999999
  rw [phi7] at h
  norm_num at h ⊢
  omega

/- ### Chebyshev-type induction step via `primorial_le_four_pow` -/

/-- Induction step: `π'(10K) < K → π'(100K) < 10K` for `K ≥ 10^6`, since the primes in
`[10K, 100K)` multiply to at most `primorial (100K) ≤ 4^(100K) < (10^7)^(9K)`. -/
theorem count_step_aux (K : ℕ) (hK : 10 ^ 6 ≤ K) (h : Nat.count Nat.Prime (10 * K) < K) :
    Nat.count Nat.Prime (100 * K) < 10 * K := by
  have hAB : 10 * K ≤ 100 * K := by omega
  have h1 : Nat.count Nat.Prime (100 * K) ≤ Nat.count Nat.Prime (10 * K) +
      (Finset.filter Nat.Prime (Finset.Ico (10 * K) (100 * K))).card := by
    rw [Nat.count_eq_card_filter_range, Nat.count_eq_card_filter_range, Finset.range_eq_Ico,
      Finset.range_eq_Ico, ← Finset.Ico_union_Ico_eq_Ico (Nat.zero_le _) hAB, Finset.filter_union]
    exact Finset.card_union_le _ _
  set S := Finset.filter Nat.Prime (Finset.Ico (10 * K) (100 * K)) with hS
  have h2 : (10 * K) ^ S.card ≤ ∏ p ∈ S, p := by
    apply Finset.pow_card_le_prod
    intro p hp
    rw [hS, Finset.mem_filter, Finset.mem_Ico] at hp
    exact hp.1.1
  have h3 : ∏ p ∈ S, p ≤ primorial (100 * K) := by
    unfold primorial
    apply Finset.prod_le_prod_of_subset_of_one_le'
    · intro p hp
      rw [hS, Finset.mem_filter, Finset.mem_Ico] at hp
      rw [Finset.mem_filter, Finset.mem_range]
      exact ⟨by omega, hp.2⟩
    · intro p hp _
      rw [Finset.mem_filter] at hp
      exact hp.2.one_lt.le
  have h4 := primorial_le_four_pow (100 * K)
  have h5 : (10 * K) ^ S.card ≤ 4 ^ (100 * K) := h2.trans (h3.trans h4)
  have h6 : S.card < 9 * K := by
    by_contra hc
    rw [not_lt] at hc
    have hK0 : K ≠ 0 := by omega
    have : 4 ^ (100 * K) < (10 * K) ^ S.card := by
      calc 4 ^ (100 * K) = (4 ^ 100) ^ K := by rw [pow_mul]
        _ < (10 ^ 63) ^ K := Nat.pow_lt_pow_left (by norm_num) hK0
        _ = (10 ^ 7) ^ (9 * K) := by rw [← pow_mul, ← pow_mul]; ring_nf
        _ ≤ (10 * K) ^ (9 * K) := Nat.pow_le_pow_left (by omega) _
        _ ≤ (10 * K) ^ S.card := Nat.pow_le_pow_right (by omega) hc
    omega
  omega

theorem count_le_ge7 (e : ℕ) : Nat.count Nat.Prime (10 ^ (e + 7)) < 10 ^ (e + 6) := by
  induction e with
  | zero => simpa using count_le_7
  | succ e ih =>
    have hK : 10 ^ 6 ≤ 10 ^ (e + 6) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h := count_step_aux (10 ^ (e + 6)) hK
      (by rw [show 10 * 10 ^ (e + 6) = 10 ^ (e + 7) by ring]; exact ih)
    rw [show 100 * 10 ^ (e + 6) = 10 ^ (e + 1 + 7) by ring,
      show 10 * 10 ^ (e + 6) = 10 ^ (e + 1 + 6) by ring] at h
    exact h

/-- `π'(10^d) < 10^(d-1)` for all `d ≥ 5`. -/
theorem count_pow_ten (d : ℕ) (hd : 5 ≤ d) : Nat.count Nat.Prime (10 ^ d) < 10 ^ (d - 1) := by
  obtain ⟨e, rfl⟩ : ∃ e, d = e + 5 := ⟨d - 5, by omega⟩
  rcases e with _ | _ | e
  · exact count_le_5
  · exact count_le_6
  · have := count_le_ge7 e
    rw [show e + 1 + 1 + 5 = e + 7 by omega, show e + 7 - 1 = e + 6 by omega]
    exact this

/- ### Cycle elements are at most 1229 -/

/-- If `k ≥ 1` and `F k` has no more digits than `k`, then `k ≤ 1229`. -/
theorem le_1229_of_numDigits {k : ℕ} (hk : 1 ≤ k) (h : numDigits (F k) ≤ numDigits k) :
    k ≤ 1229 := by
  have hp : (Nat.nth Nat.Prime (k - 1)).Prime := Nat.prime_nth_prime _
  rw [numDigits_F] at h
  have hplt : Nat.nth Nat.Prime (k - 1) < 10 ^ numDigits k :=
    (Nat.digits_length_le_iff (by norm_num) _).mp h
  have hkd : 10 ^ numDigits k ≤ 10 * k := Nat.base_pow_length_digits_le 10 k (by norm_num) (by omega)
  have hcount : Nat.count Nat.Prime (Nat.nth Nat.Prime (k - 1) + 1) = k := by
    rw [Nat.count_succ, if_pos hp, Nat.count_nth_of_infinite Nat.infinite_setOfPred_prime]
    omega
  have hk_le : k ≤ Nat.count Nat.Prime (10 ^ numDigits k) :=
    calc k = Nat.count Nat.Prime (Nat.nth Nat.Prime (k - 1) + 1) := hcount.symm
      _ ≤ Nat.count Nat.Prime (10 ^ numDigits k) := Nat.count_monotone _ hplt
  by_cases h5 : 5 ≤ numDigits k
  · have h1 := count_pow_ten (numDigits k) h5
    have h2 : 10 * 10 ^ (numDigits k - 1) = 10 ^ numDigits k := by
      rw [← _root_.pow_succ']
      congr 1
      omega
    omega
  · have h1 : Nat.count Nat.Prime (10 ^ numDigits k) ≤ Nat.count Nat.Prime 10000 := by
      apply Nat.count_monotone
      calc 10 ^ numDigits k ≤ 10 ^ 4 := Nat.pow_le_pow_right (by norm_num) (by omega)
        _ = 10000 := by norm_num
    rw [table_facts.1] at h1
    omega

/- ### Main theorem -/

/-- **Negative answer to A100475**: no positive start value gives an ultimately periodic
sequence (in particular none other than `1`). -/
theorem not_conjecture :
    ¬ ∃ x : ℕ, 0 < x ∧ x ≠ 1 ∧ IsUltimatelyPeriodic (aStartAt x) := by
  rintro ⟨x, hx, -, N, P, hP, hper⟩
  have hpos : ∀ n, 1 ≤ aStartAt x n := fun n =>
    Nat.one_le_iff_ne_zero.mpr (aStartAt_ne_zero hx n)
  have hmono : Monotone (fun n => numDigits (aStartAt x n)) := by
    apply monotone_nat_of_le_succ
    intro n
    rw [aStartAt_succ' hx]
    exact numDigits_le_F (hpos n)
  have hbound : ∀ n, N ≤ n → aStartAt x n ≤ 1229 := by
    intro n hn
    apply le_1229_of_numDigits (hpos n)
    rw [← aStartAt_succ' hx]
    calc numDigits (aStartAt x (n + 1)) ≤ numDigits (aStartAt x (n + P)) := hmono (by omega)
      _ = numDigits (aStartAt x n) := by rw [hper n hn]
  obtain ⟨j, hj⟩ := escapes (hpos N) (hbound N le_rfl)
  rw [← aStartAt_add hx] at hj
  have := hbound (N + j) (by omega)
  omega

end OeisA100475

/-- The statement, spelled out with fully qualified names. -/
example : ¬ ∃ x : ℕ, 0 < x ∧ x ≠ 1 ∧
    OeisA100475.IsUltimatelyPeriodic (OeisA100475.aStartAt x) :=
  OeisA100475.not_conjecture
