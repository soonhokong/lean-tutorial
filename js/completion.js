var completions = [
Exists.intro|Π (a : ?A), ?P a → Exists ?P
Exists.rec_on|Exists ?P → (Π (a : ?A), ?P a → ?C) → ?C
Prodl_eq_pow_of_const|Π (b : ?B), (∀ (a : ?A), list.mem a ?l → ?f a = b) → Prodl ?l ?f = b ^ list.length ?l
Suml_zero|∀ (l : list ?A), (∑ (x : ?A)←l, 0) = 0
abs.by_cases|?P ?a → ?P (-?a) → ?P (abs ?a)
abs_abs|∀ (a : ?A), abs (abs a) = abs a
abs_add_three|∀ (a b c : ?A), abs (a + b + c) ≤ abs a + abs b + abs c
abs_div|∀ (a b : ?A), abs (a / b) = abs a / abs b
abs_dvd_iff|∀ (a b : ?A), abs a ∣ b ↔ a ∣ b
abs_dvd_of_dvd|?a ∣ ?b → abs ?a ∣ ?b
abs_mul_self|∀ (a : ?A), abs (a * a) = a * a
abs_mul|∀ (a b : ?A), abs (a * b) = abs a * abs b
abs_neg|∀ (a : ?A), abs (-a) = abs a
abs_nonneg|∀ (a : ?A), abs a ≥ 0
abs_of_neg|?a < 0 → abs ?a = -?a
abs_of_nonneg|?a ≥ 0 → abs ?a = ?a
abs_of_nonpos|?a ≤ 0 → abs ?a = -?a
abs_of_pos|?a > 0 → abs ?a = ?a
abs_one_div|∀ (a : ?A), abs (1 / a) = 1 / abs a
abs_pos_of_neg|?a < 0 → abs ?a > 0
abs_pos_of_pos|?a > 0 → abs ?a > 0
abs_pow|∀ (a : ?A) (n : ℕ), abs (a ^ n) = abs a ^ n
abs_sub_le|∀ (a b c : ?A), abs (a - c) ≤ abs (a - b) + abs (b - c)
abs_sub_square|∀ (a b : ?A), abs (a - b) * abs (a - b) = a * a + b * b - (1 + 1) * a * b
abs_sub|∀ (a b : ?A), abs (a - b) = abs (b - a)
abs_zero|abs 0 = 0
absurd|?a → ¬?a → ?b
abs|?A → ?A
acc.cases_on|acc ?R ?a → (Π (x : ?A), (Π (y : ?A), ?R y x → acc ?R y) → ?C x) → ?C ?a
acc.drec|(Π (x : ?A) (acx : Π (y : ?A), ?R y x → acc ?R y), (Π (y : ?A) (ryx : ?R y x), ?C y (acx y ryx)) → ?C x (acc.intro x acx)) → (Π {a : ?A} (h₂ : acc ?R a), ?C a h₂)
acc.intro|Π (x : ?A), (Π (y : ?A), ?R y x → acc ?R y) → acc ?R x
acc.inv|acc ?R ?x → ?R ?y ?x → acc ?R ?y
acc.rec_on|acc ?R ?a → (Π (x : ?A), (Π (y : ?A), ?R y x → acc ?R y) → (Π (y : ?A), ?R y x → ?C y) → ?C x) → ?C ?a
acc.rec|(Π (x : ?A), (Π (y : ?A), ?R y x → acc ?R y) → (Π (y : ?A), ?R y x → ?C y) → ?C x) → (Π {a : ?A}, acc ?R a → ?C a)
acc|(?A → ?A → Prop) → ?A → Prop
add.assoc|∀ (a b c : ?A), (:a + b + c:) = (:a + (b + c):)
add.comm4|∀ (n m k l : ?A), n + m + (k + l) = n + k + (m + l)
add.comm|∀ (a b : ?A), a + b = b + a
add.left_comm|∀ (a b c : ?A), a + (b + c) = b + (a + c)
add.left_inv|∀ (a : ?A), -a + a = 0
add.right_comm|∀ (a b c : ?A), a + b + c = a + c + b
add.right_inv|∀ (a : ?A), a + -a = 0
add_comm_group|Type → Type
add_comm_three|∀ (a b c : ?A), a + b + c = c + b + a
add_group._trans_of_to_add_right_cancel_semigroup_1|add_semigroup ?A
add_group.mk|Π (add : ?A → ?A → ?A), (∀ (a b c : ?A), add (add a b) c = add a (add b c)) → (Π (zero : ?A), (∀ (a : ?A), add zero a = a) → (∀ (a : ?A), add a zero = a) → (Π (neg : ?A → ?A), (∀ (a : ?A), add (neg a) a = zero) → add_group ?A))
add_group.rec|(Π (add : ?A → ?A → ?A) (add_assoc : ∀ (a b c : ?A), add (add a b) c = add a (add b c)) (zero : ?A) (zero_add : ∀ (a : ?A), add zero a = a) (add_zero : ∀ (a : ?A), add a zero = a) (neg : ?A → ?A) (add_left_inv : ∀ (a : ?A), add (neg a) a = zero), ?C (add_group.mk add add_assoc zero zero_add add_zero neg add_left_inv)) → (Π (n : add_group ?A), ?C n)
add_group|Type → Type
add_halves|∀ (a : ?A), a / 2 + a / 2 = a
add_imul|∀ (i j : ℤ) (a : ?A), imul (i + j) a = imul i a + imul j a
add_le_add_left|?a ≤ ?b → (∀ (c : ?A), c + ?a ≤ c + ?b)
add_le_add|?a ≤ ?b → ?c ≤ ?d → ?a + ?c ≤ ?b + ?d
add_le_of_le_sub_right|?a ≤ ?c - ?b → ?a + ?b ≤ ?c
add_left_cancel|?a + ?b = ?a + ?c → ?b = ?c
add_lt_add_left|?a < ?b → (∀ (c : ?A), c + ?a < c + ?b)
add_lt_add|?a < ?b → ?c < ?d → ?a + ?c < ?b + ?d
add_lt_iff_lt_neg_add_right|∀ (a b c : ?A), a + b < c ↔ a < -b + c
add_lt_of_lt_sub_left|?b < ?c - ?a → ?a + ?b < ?c
add_midpoint|?a < ?b → ?a + (?b - ?a) / 2 < ?b
add_monoid.mk|Π (add : ?A → ?A → ?A), (∀ (a b c : ?A), add (add a b) c = add a (add b c)) → (Π (zero : ?A), (∀ (a : ?A), add zero a = a) → (∀ (a : ?A), add a zero = a) → add_monoid ?A)
add_monoid.rec|(Π (add : ?A → ?A → ?A) (add_assoc : ∀ (a b c : ?A), add (add a b) c = add a (add b c)) (zero : ?A) (zero_add : ∀ (a : ?A), add zero a = a) (add_zero : ∀ (a : ?A), add a zero = a), ?C (add_monoid.mk add add_assoc zero zero_add add_zero)) → (Π (n : add_monoid ?A), ?C n)
add_monoid.to_has_zero|Π (A : Type) [s : add_monoid A], has_zero A
add_monoid|Type → Type
add_neg_cancel_left|∀ (a b : ?A), a + (-a + b) = b
add_neg_eq_of_eq_add|?a = ?c + ?b → ?a + -?b = ?c
add_neg|?a < 0 → ?b < 0 → ?a + ?b < 0
add_nmul|∀ (m n : ℕ) (a : ?A), (m + n)⬝a = m⬝a + n⬝a
add_nonneg|0 ≤ ?a → 0 ≤ ?b → 0 ≤ ?a + ?b
add_nonpos|?a ≤ 0 → ?b ≤ 0 → ?a + ?b ≤ 0
add_pos|0 < ?a → 0 < ?b → 0 < ?a + ?b
add_quarters|∀ (a : ?A), a / 4 + a / 4 = a / 2
add_right_cancel_semigroup.no_confusion_type|Type → add_right_cancel_semigroup ?A → add_right_cancel_semigroup ?A → Type
add_semigroup|Type → Type
add_sub_assoc|∀ (a b c : ?A), a + b - c = a + (b - c)
add_sub_cancel|∀ (a b : ?A), a + b - b = a
add_sub_comm|∀ (a b c d : ?A), a + b - (c + d) = a - c + (b - d)
add_sub|∀ (a b c : ?A), a + (b - c) = a + b - c
add_zero|∀ (a : ?A), a + 0 = a
add|?A → ?A → ?A
algebra.div|?A → ?A → ?A
algebra.dvd|?A → ?A → Prop
algebra.prio|num
algebra.sub|?A → ?A → ?A
all_of_check_pred_eq_tt|check_pred ?p ?l = bool.tt → (Π {a : ?A}, list.mem a ?l → ?p a)
and.assoc|(?a ∧ ?b) ∧ ?c ↔ ?a ∧ ?b ∧ ?c
and.cases_on|?a ∧ ?b → (?a → ?b → ?C) → ?C
and.comm|?a ∧ ?b ↔ ?b ∧ ?a
and.elim_left|?a ∧ ?b → ?a
and.elim_right|?a ∧ ?b → ?b
and.elim|?a ∧ ?b → (?a → ?b → ?c) → ?c
and.imp_left|(?a → ?b) → ?a ∧ ?c → ?b ∧ ?c
and.imp_right|(?a → ?b) → ?c ∧ ?a → ?c ∧ ?b
and.imp|(?a → ?c) → (?b → ?d) → ?a ∧ ?b → ?c ∧ ?d
and.intro|?a → ?b → ?a ∧ ?b
and.left_comm|?a ∧ ?b ∧ ?c ↔ ?b ∧ ?a ∧ ?c
and.left|?a ∧ ?b → ?a
and.rec_on|?a ∧ ?b → (?a → ?b → ?C) → ?C
and.rec|(?a → ?b → ?C) → ?a ∧ ?b → ?C
and.right_comm|∀ (a b c : Prop), (a ∧ b) ∧ c ↔ (a ∧ c) ∧ b
and.right|?a ∧ ?b → ?b
and.swap|?a ∧ ?b → ?b ∧ ?a
and_congr|(?a ↔ ?c) → (?b ↔ ?d) → (?a ∧ ?b ↔ ?c ∧ ?d)
and_false|∀ (a : Prop), a ∧ false ↔ false
and_iff_left|?b → (?a ∧ ?b ↔ ?a)
and_iff_right|?a → (?a ∧ ?b ↔ ?b)
and_imp_eq|∀ (a b c : Prop), (a ∧ b → c) = (a → b → c)
and_imp_iff|∀ (a b c : Prop), a ∧ b → c ↔ a → b → c
and_not_self|∀ (a : Prop), a ∧ ¬a ↔ false
and_self|∀ (a : Prop), a ∧ a ↔ a
and_true|∀ (a : Prop), a ∧ true ↔ a
and|Prop → Prop → Prop
anti_symmetric|(?B → ?B → Prop) → Prop
arbitrary|Π (A : Type) [H : inhabited A], A
binary.assoc4helper|binary.associative ?f → (∀ (a b c d : ?A), ?f (?f a b) (?f c d) = ?f a (?f (?f b c) d))
binary.associative|(?A → ?A → ?A) → Prop
binary.comm4|binary.commutative ?f → binary.associative ?f → (∀ (a b c d : ?A), ?f (?f a b) (?f c d) = ?f (?f a c) (?f b d))
binary.commutative|(?A → ?A → ?A) → Prop
binary.inv_op_cancel_left|(?A → ?A → ?A) → (?A → ?A) → Prop
binary.inv_op_cancel_right|(?A → ?A → ?A) → (?A → ?A) → Prop
binary.left_cancelative|(?A → ?A → ?A) → Prop
binary.left_commutative_compose_left|∀ (f : ?A → ?A → ?A) (g : ?B → ?A), binary.left_commutative f → binary.left_commutative (function.comp_left f g)
binary.left_commutative|(?A → ?B → ?B) → Prop
binary.left_comm|binary.commutative ?f → binary.associative ?f → binary.left_commutative ?f
binary.left_distributive|(?A → ?A → ?A) → (?A → ?A → ?A) → Prop
binary.left_identity|(?A → ?A → ?A) → ?A → Prop
binary.left_inverse|(?A → ?A → ?A) → (?A → ?A) → ?A → Prop
binary.op_inv_cancel_left|(?A → ?A → ?A) → (?A → ?A) → Prop
binary.op_inv_cancel_right|(?A → ?A → ?A) → (?A → ?A) → Prop
binary.right_cancelative|(?A → ?A → ?A) → Prop
binary.right_commutative_comp_right|∀ (f : ?A → ?A → ?A) (g : ?B → ?A), binary.right_commutative f → binary.right_commutative (function.comp_right f g)
binary.right_commutative|(?B → ?A → ?B) → Prop
binary.right_comm|binary.commutative ?f → binary.associative ?f → binary.right_commutative ?f
binary.right_distributive|(?A → ?A → ?A) → (?A → ?A → ?A) → Prop
binary.right_identity|(?A → ?A → ?A) → ?A → Prop
binary.right_inverse|(?A → ?A → ?A) → (?A → ?A) → ?A → Prop
bit0|?A → ?A
bit1|?A → ?A
bool.absurd_of_eq_ff_of_eq_tt|?a = bool.ff → ?a = bool.tt → ?B
bool.band_assoc|∀ (a b c : bool), bool.band (bool.band a b) c = bool.band a (bool.band b c)
bool.band_comm|∀ (a b : bool), bool.band a b = bool.band b a
bool.band_elim_left|bool.band ?a ?b = bool.tt → ?a = bool.tt
bool.band_elim_right|bool.band ?a ?b = bool.tt → ?b = bool.tt
bool.band_ff|∀ (a : bool), bool.band a bool.ff = bool.ff
bool.band_intro|?a = bool.tt → ?b = bool.tt → bool.band ?a ?b = bool.tt
bool.band_left_comm|∀ (a b c : bool), bool.band a (bool.band b c) = bool.band b (bool.band a c)
bool.band_self|∀ (a : bool), bool.band a a = a
bool.band_tt|∀ (a : bool), bool.band a bool.tt = a
bool.band|bool → bool → bool
bool.bnot_bnot|∀ (a : bool), bool.bnot (bool.bnot a) = a
bool.bnot_false|bool.bnot bool.ff = bool.tt
bool.bnot_true|bool.bnot bool.tt = bool.ff
bool.bnot|bool → bool
bool.bor_assoc|∀ (a b c : bool), bool.bor (bool.bor a b) c = bool.bor a (bool.bor b c)
bool.bor_comm|∀ (a b : bool), bool.bor a b = bool.bor b a
bool.bor_ff|∀ (a : bool), bool.bor a bool.ff = a
bool.bor_inl|?a = bool.tt → bool.bor ?a ?b = bool.tt
bool.bor_inr|?b = bool.tt → bool.bor ?a ?b = bool.tt
bool.bor_left_comm|∀ (a b c : bool), bool.bor a (bool.bor b c) = bool.bor b (bool.bor a c)
bool.bor_self|∀ (a : bool), bool.bor a a = a
bool.bor_tt|∀ (a : bool), bool.bor a bool.tt = bool.tt
bool.bor|bool → bool → bool
bool.bxor_assoc|∀ (a b c : bool), bool.bxor (bool.bxor a b) c = bool.bxor a (bool.bxor b c)
bool.bxor_comm|∀ (a b : bool), bool.bxor a b = bool.bxor b a
bool.bxor_ff|∀ (a : bool), bool.bxor a bool.ff = a
bool.bxor_left_comm|∀ (a b c : bool), bool.bxor a (bool.bxor b c) = bool.bxor b (bool.bxor a c)
bool.bxor_self|∀ (a : bool), bool.bxor a a = bool.ff
bool.bxor_tt|∀ (a : bool), bool.bxor a bool.tt = bool.bnot a
bool.bxor|bool → bool → bool
bool.cases_on|Π (n : bool), ?C bool.ff → ?C bool.tt → ?C n
bool.cond_ff|∀ (t e : ?A), bool.cond bool.ff t e = e
bool.cond_tt|∀ (t e : ?A), bool.cond bool.tt t e = t
bool.cond|bool → ?A → ?A → ?A
bool.dichotomy|∀ (b : bool), b = bool.ff ∨ b = bool.tt
bool.eq_ff_of_bnot_eq_tt|bool.bnot ?a = bool.tt → ?a = bool.ff
bool.eq_ff_of_ne_tt|?a ≠ bool.tt → ?a = bool.ff
bool.eq_tt_of_bnot_eq_ff|bool.bnot ?a = bool.ff → ?a = bool.tt
bool.eq_tt_of_ne_ff|?a ≠ bool.ff → ?a = bool.tt
bool.ff_band|∀ (a : bool), bool.band bool.ff a = bool.ff
bool.ff_bor|∀ (a : bool), bool.bor bool.ff a = a
bool.ff_bxor_ff|bool.bxor bool.ff bool.ff = bool.ff
bool.ff_bxor_tt|bool.bxor bool.ff bool.tt = bool.tt
bool.ff_bxor|∀ (a : bool), bool.bxor bool.ff a = a
bool.ff_ne_tt|bool.ff = bool.tt → false
bool.ff|bool
bool.has_decidable_eq|Π (a b : bool), decidable (a = b)
bool.induction_on|Π (n : bool), ?C bool.ff → ?C bool.tt → ?C n
bool.is_inhabited|inhabited bool
bool.measurable|measurable bool
bool.no_confusion_type|Type → bool → bool → Type
bool.no_confusion|?v1 = ?v2 → bool.no_confusion_type ?P ?v1 ?v2
bool.or_of_bor_eq|bool.bor ?a ?b = bool.tt → ?a = bool.tt ∨ ?b = bool.tt
bool.rec_on|Π (n : bool), ?C bool.ff → ?C bool.tt → ?C n
bool.rec|?C bool.ff → ?C bool.tt → (Π (n : bool), ?C n)
bool.tt_band|∀ (a : bool), bool.band bool.tt a = a
bool.tt_bor|∀ (a : bool), bool.bor bool.tt a = bool.tt
bool.tt_bxor_ff|bool.bxor bool.tt bool.ff = bool.tt
bool.tt_bxor_tt|bool.bxor bool.tt bool.tt = bool.ff
bool.tt_bxor|∀ (a : bool), bool.bxor bool.tt a = bool.bnot a
bool.tt|bool
bool|Type₁
bot_le|∀ (a : ?A), ⊥ ≤ a
bot|?A
cast_app|∀ (H : ?P = ?P') (f : Π (x : ?A), ?P x) (a : ?A), cast (pi_eq H) f a == f a
cast_eq|∀ (H : ?A = ?A) (a : ?A), cast H a = a
cast_heq|∀ (H : ?A = ?B) (a : ?A), cast H a == a
cast_proof_irrel|∀ (H₁ H₂ : ?A = ?B) (a : ?A), cast H₁ a = cast H₂ a
cast_to_heq|cast ?H₁ ?a = ?b → ?a == ?b
cast_trans|∀ (Hab : ?A = ?B) (Hbc : ?B = ?C) (a : ?A), cast Hbc (cast Hab a) = cast (eq.trans Hab Hbc) a
cast|?A = ?B → ?A → ?B
char.cases_on|Π (n : char), (Π (a a_1 a_2 a_3 a_4 a_5 a_6 a_7 : bool), ?C (char.mk a a_1 a_2 a_3 a_4 a_5 a_6 a_7)) → ?C n
char.is_inhabited|inhabited char
char.mk|bool → bool → bool → bool → bool → bool → bool → bool → char
char.no_confusion|?v1 = ?v2 → char.no_confusion_type ?P ?v1 ?v2
char.rec_on|Π (n : char), (Π (a a_1 a_2 a_3 a_4 a_5 a_6 a_7 : bool), ?C (char.mk a a_1 a_2 a_3 a_4 a_5 a_6 a_7)) → ?C n
char.rec|(Π (a a_1 a_2 a_3 a_4 a_5 a_6 a_7 : bool), ?C (char.mk a a_1 a_2 a_3 a_4 a_5 a_6 a_7)) → (Π (n : char), ?C n)
char|Type₁
check_pred|Π (p : ?A → Prop) [h : decidable_pred p], list ?A → bool
classical.em|∀ (p : Prop), p ∨ ¬p
classical.epsilon|(?A → Prop) → ?A
classical.skolem|(∀ (x : ?A), Exists (?P x)) ↔ ∃ (f : Π (a_3 : ?A), ?B a_3), Π (x : ?A), ?P x (f x)
classical.some|Exists ?P → ?A
comm_group.mk|Π (mul : ?A → ?A → ?A), (∀ (a b c : ?A), mul (mul a b) c = mul a (mul b c)) → (Π (one : ?A), (∀ (a : ?A), mul one a = a) → (∀ (a : ?A), mul a one = a) → (Π (inv : ?A → ?A), (∀ (a : ?A), mul (inv a) a = one) → (∀ (a b : ?A), mul a b = mul b a) → comm_group ?A))
comm_group.no_confusion_type|Type → comm_group ?A → comm_group ?A → Type
comm_group.rec|(Π (mul : ?A → ?A → ?A) (mul_assoc : ∀ (a b c : ?A), mul (mul a b) c = mul a (mul b c)) (one : ?A) (one_mul : ∀ (a : ?A), mul one a = a) (mul_one : ∀ (a : ?A), mul a one = a) (inv : ?A → ?A) (mul_left_inv : ∀ (a : ?A), mul (inv a) a = one) (mul_comm : ∀ (a b : ?A), mul a b = mul b a), ?C (comm_group.mk mul mul_assoc one one_mul mul_one inv mul_left_inv mul_comm)) → (Π (n : comm_group ?A), ?C n)
comm_group.to_comm_monoid|Π (A : Type) [s : comm_group A], comm_monoid A
comm_group|Type → Type
comm_monoid.mk|Π (mul : ?A → ?A → ?A), (∀ (a b c : ?A), mul (mul a b) c = mul a (mul b c)) → (Π (one : ?A), (∀ (a : ?A), mul one a = a) → (∀ (a : ?A), mul a one = a) → (∀ (a b : ?A), mul a b = mul b a) → comm_monoid ?A)
comm_monoid.rec|(Π (mul : ?A → ?A → ?A) (mul_assoc : ∀ (a b c : ?A), mul (mul a b) c = mul a (mul b c)) (one : ?A) (one_mul : ∀ (a : ?A), mul one a = a) (mul_one : ∀ (a : ?A), mul a one = a) (mul_comm : ∀ (a b : ?A), mul a b = mul b a), ?C (comm_monoid.mk mul mul_assoc one one_mul mul_one mul_comm)) → (Π (n : comm_monoid ?A), ?C n)
comm_monoid|Type → Type
comm_ring.mk|Π (add : ?A → ?A → ?A), (∀ (a b c : ?A), add (add a b) c = add a (add b c)) → (Π (zero : ?A), (∀ (a : ?A), add zero a = a) → (∀ (a : ?A), add a zero = a) → (Π (neg : ?A → ?A), (∀ (a : ?A), add (neg a) a = zero) → (∀ (a b : ?A), add a b = add b a) → (Π (mul : ?A → ?A → ?A), (∀ (a b c : ?A), mul (mul a b) c = mul a (mul b c)) → (Π (one : ?A), (∀ (a : ?A), mul one a = a) → (∀ (a : ?A), mul a one = a) → (∀ (a b c : ?A), mul a (add b c) = add (mul a b) (mul a c)) → (∀ (a b c : ?A), mul (add a b) c = add (mul a c) (mul b c)) → (∀ (a b : ?A), mul a b = mul b a) → comm_ring ?A))))
comm_ring.rec_on|Π (n : comm_ring ?A), (Π (add : ?A → ?A → ?A) (add_assoc : ∀ (a b c : ?A), add (add a b) c = add a (add b c)) (zero : ?A) (zero_add : ∀ (a : ?A), add zero a = a) (add_zero : ∀ (a : ?A), add a zero = a) (neg : ?A → ?A) (add_left_inv : ∀ (a : ?A), add (neg a) a = zero) (add_comm : ∀ (a b : ?A), add a b = add b a) (mul : ?A → ?A → ?A) (mul_assoc : ∀ (a b c : ?A), mul (mul a b) c = mul a (mul b c)) (one : ?A) (one_mul : ∀ (a : ?A), mul one a = a) (mul_one : ∀ (a : ?A), mul a one = a) (left_distrib : ∀ (a b c : ?A), mul a (add b c) = add (mul a b) (mul a c)) (right_distrib : ∀ (a b c : ?A), mul (add a b) c = add (mul a c) (mul b c)) (mul_comm : ∀ (a b : ?A), mul a b = mul b a), ?C (comm_ring.mk add add_assoc zero zero_add add_zero neg add_left_inv add_comm mul mul_assoc one one_mul mul_one left_distrib right_distrib mul_comm)) → ?C n
comm_ring.rec|(Π (add : ?A → ?A → ?A) (add_assoc : ∀ (a b c : ?A), add (add a b) c = add a (add b c)) (zero : ?A) (zero_add : ∀ (a : ?A), add zero a = a) (add_zero : ∀ (a : ?A), add a zero = a) (neg : ?A → ?A) (add_left_inv : ∀ (a : ?A), add (neg a) a = zero) (add_comm : ∀ (a b : ?A), add a b = add b a) (mul : ?A → ?A → ?A) (mul_assoc : ∀ (a b c : ?A), mul (mul a b) c = mul a (mul b c)) (one : ?A) (one_mul : ∀ (a : ?A), mul one a = a) (mul_one : ∀ (a : ?A), mul a one = a) (left_distrib : ∀ (a b c : ?A), mul a (add b c) = add (mul a b) (mul a c)) (right_distrib : ∀ (a b c : ?A), mul (add a b) c = add (mul a c) (mul b c)) (mul_comm : ∀ (a b : ?A), mul a b = mul b a), ?C (comm_ring.mk add add_assoc zero zero_add add_zero neg add_left_inv add_comm mul mul_assoc one one_mul mul_one left_distrib right_distrib mul_comm)) → (Π (n : comm_ring ?A), ?C n)
comm_ring.to_ring|Π (A : Type) [s : comm_ring A], ring A
comm_ring|Type → Type
comm_semigroup.mk|Π (mul : ?A → ?A → ?A), (∀ (a b c : ?A), mul (mul a b) c = mul a (mul b c)) → (∀ (a b : ?A), mul a b = mul b a) → comm_semigroup ?A
comm_semigroup|Type → Type
comm_semiring.mk|Π (add : ?A → ?A → ?A), (∀ (a b c : ?A), add (add a b) c = add a (add b c)) → (Π (zero : ?A), (∀ (a : ?A), add zero a = a) → (∀ (a : ?A), add a zero = a) → (∀ (a b : ?A), add a b = add b a) → (Π (mul : ?A → ?A → ?A), (∀ (a b c : ?A), mul (mul a b) c = mul a (mul b c)) → (Π (one : ?A), (∀ (a : ?A), mul one a = a) → (∀ (a : ?A), mul a one = a) → (∀ (a b c : ?A), mul a (add b c) = add (mul a b) (mul a c)) → (∀ (a b c : ?A), mul (add a b) c = add (mul a c) (mul b c)) → (∀ (a : ?A), mul zero a = zero) → (∀ (a : ?A), mul a zero = zero) → (∀ (a b : ?A), mul a b = mul b a) → comm_semiring ?A)))
comm_semiring.no_confusion_type|Type → comm_semiring ?A → comm_semiring ?A → Type
comm_semiring|Type → Type
complete_lattice.mk|Π (le : ?A → ?A → Prop), (∀ (a : ?A), le a a) → (∀ (a b c : ?A), le a b → le b c → le a c) → (∀ (a b : ?A), le a b → le b a → a = b) → (Π (inf sup : ?A → ?A → ?A), (∀ (a b : ?A), le (inf a b) a) → (∀ (a b : ?A), le (inf a b) b) → (∀ (a b c : ?A), le c a → le c b → le c (inf a b)) → (∀ (a b : ?A), le a (sup a b)) → (∀ (a b : ?A), le b (sup a b)) → (∀ (a b c : ?A), le a c → le b c → le (sup a b) c) → (Π (Inf Sup : set ?A → ?A), (∀ {a : ?A} {s : set ?A}, set.mem a s → le (Inf s) a) → (Π {b : ?A} {s : set ?A}, (∀ (a : ?A), set.mem a s → le b a) → le b (Inf s)) → (∀ {a : ?A} {s : set ?A}, set.mem a s → le a (Sup s)) → (Π {b : ?A} {s : set ?A}, (∀ (a : ?A), set.mem a s → le a b) → le (Sup s) b) → complete_lattice ?A))
complete_lattice_Inf._trans_of_to_weak_order|Π (A : Type) [s : complete_lattice_Inf A], has_le A
complete_lattice_Inf.mk|Π (le : ?A → ?A → Prop), (∀ (a : ?A), le a a) → (∀ (a b c : ?A), le a b → le b c → le a c) → (∀ (a b : ?A), le a b → le b a → a = b) → (Π (Inf : set ?A → ?A), (∀ {a : ?A} {s : set ?A}, set.mem a s → le (Inf s) a) → (Π {b : ?A} {s : set ?A}, (∀ (a : ?A), set.mem a s → le b a) → le b (Inf s)) → complete_lattice_Inf ?A)
complete_lattice_Sup._trans_of_to_weak_order|Π (A : Type) [s : complete_lattice_Sup A], has_le A
complete_lattice_Sup.mk|Π (le : ?A → ?A → Prop), (∀ (a : ?A), le a a) → (∀ (a b c : ?A), le a b → le b c → le a c) → (∀ (a b : ?A), le a b → le b a → a = b) → (Π (Sup : set ?A → ?A), (∀ {a : ?A} {s : set ?A}, set.mem a s → le a (Sup s)) → (Π {b : ?A} {s : set ?A}, (∀ (a : ?A), set.mem a s → le a b) → le (Sup s) b) → complete_lattice_Sup ?A)
complete_lattice_Sup.no_confusion_type|Type → complete_lattice_Sup ?A → complete_lattice_Sup ?A → Type
complete_lattice_Sup.to_weak_order|Π (A : Type) [s : complete_lattice_Sup A], weak_order A
complete_lattice_Sup|Type → Type
complete_lattice|Type → Type
complex._trans_of_discrete_field_11|add_left_cancel_semigroup ℂ
complex._trans_of_discrete_field_12|add_right_cancel_semigroup ℂ
complex._trans_of_discrete_field_14|monoid ℂ
complex._trans_of_discrete_field_16|has_add ℂ
complex._trans_of_discrete_field_17|semiring ℂ
complex._trans_of_discrete_field_20|no_zero_divisors ℂ
complex._trans_of_discrete_field_23|has_one ℂ
complex._trans_of_discrete_field_24|has_zero ℂ
complex._trans_of_discrete_field_5|add_comm_group ℂ
complex._trans_to_of_real_1|ℕ → ℂ
complex.add_assoc|∀ (w z u : ℂ), w + z + u = w + (z + u)
complex.add_comm|∀ (w z : ℂ), w + z = z + w
complex.add_def|∀ (z w : ℂ), z + w = complex.mk (complex.re z + complex.re w) (complex.im z + complex.im w)
complex.add_zero|∀ (z : ℂ), z + 0 = z
complex.add|ℂ → ℂ → ℂ
complex.cases_on|Π (n : ℂ), (Π (re im : real), ?C (complex.mk re im)) → ?C n
complex.cmod_conj|∀ (z : ℂ), complex.cmod (complex.conj z) = complex.cmod z
complex.cmod_mul|∀ (z w : ℂ), complex.cmod (z * w) = complex.cmod z * complex.cmod w
complex.cmod|ℂ → real
complex.comm_ring|comm_ring ℂ
complex.complex_has_mul|has_mul ℂ
complex.complex_has_neg|has_neg ℂ
complex.conj_add|∀ (z w : ℂ), complex.conj (z + w) = complex.conj z + complex.conj w
complex.conj_conj|∀ (z : ℂ), complex.conj (complex.conj z) = z
complex.conj_inv|∀ (z : ℂ), (complex.conj z)⁻¹ = complex.conj z⁻¹
complex.conj_mul|∀ (z w : ℂ), complex.conj (z * w) = complex.conj z * complex.conj w
complex.conj|ℂ → ℂ
complex.destruct|Π (n : ℂ), (Π (re im : real), ?C (complex.mk re im)) → ?C n
complex.div_def|∀ (z w : ℂ), z / w = z * w⁻¹
complex.div|ℂ → ℂ → ℂ
complex.eq|complex.re ?z = complex.re ?w → complex.im ?z = complex.im ?w → ?z = ?w
complex.eta|∀ (z : ℂ), complex.mk (complex.re z) (complex.im z) = z
complex.i_mul_i|complex.ii * complex.ii = -1
complex.ii|ℂ
complex.im_add|∀ (z w : ℂ), complex.im (z + w) = complex.im z + complex.im w
complex.inv_def|∀ (z : ℂ), z⁻¹ = complex.conj z * complex.of_real (complex.cmod z)⁻¹
complex.inv_zero|0⁻¹ = 0
complex.inv|ℂ → ℂ
complex.left_distrib|∀ (u w z : ℂ), u * (w + z) = u * w + u * z
complex.mk|real → real → ℂ
complex.mul_assoc|∀ (u w z : ℂ), u * w * z = u * (w * z)
complex.mul_comm|∀ (w z : ℂ), w * z = z * w
complex.mul_def|∀ (z w : ℂ), z * w = complex.mk (complex.re w * complex.re z - complex.im w * complex.im z) (complex.re w * complex.im z + complex.im w * complex.re z)
complex.mul_one|∀ (z : ℂ), z * 1 = z
complex.mul|ℂ → ℂ → ℂ
complex.neg_def|∀ (z : ℂ), -z = complex.mk (-complex.re z) (-complex.im z)
complex.neg|ℂ → ℂ
complex.of_int.inj|complex.of_int ?a = complex.of_int ?b → ?a = ?b
complex.of_int_eq_of_int_iff|∀ (a b : ℤ), complex.of_int a = complex.of_int b ↔ a = b
complex.of_int_eq|∀ (a : ℤ), complex.of_int a = complex.of_real (real.of_int a)
complex.of_int|ℤ → ℂ
complex.of_nat.inj|complex.of_nat ?a = complex.of_nat ?b → ?a = ?b
complex.of_nat_eq_of_nat_iff|∀ (a b : ℕ), complex.of_nat a = complex.of_nat b ↔ a = b
complex.of_nat|ℕ → ℂ
complex.of_num|num → ℂ
complex.of_rat.inj|complex.of_rat ?x = complex.of_rat ?y → ?x = ?y
complex.of_rat_add|∀ (a b : ℚ), complex.of_rat (a + b) = complex.of_rat a + complex.of_rat b
complex.of_rat_eq|∀ (a : ℚ), complex.of_rat a = complex.of_real (real.of_rat a)
complex.of_rat|ℚ → ℂ
complex.of_real.inj|complex.of_real ?a = complex.of_real ?b → ?a = ?b
complex.of_real_mul|∀ (a b : real), complex.of_real (a * b) = complex.of_real a * complex.of_real b
complex.of_real|real → ℂ
complex.one_mul|∀ (z : ℂ), 1 * z = z
complex.prio|num
complex.re_add|∀ (z w : ℂ), complex.re (z + w) = complex.re z + complex.re w
complex.rec_on|Π (n : ℂ), (Π (re im : real), ?C (complex.mk re im)) → ?C n
complex.rec|(Π (re im : real), ?C (complex.mk re im)) → (Π (n : ℂ), ?C n)
complex.smul|real → ℂ → ℂ
complex.zero_add|∀ (z : ℂ), 0 + z = z
complex|Type₁
congr2|∀ (f f' : ?A → ?B → ?C), f = f' → ?a = ?a' → ?b = ?b' → f ?a ?b = f' ?a' ?b'
congr3|∀ (f f' : ?A → ?B → ?C → ?D), f = f' → ?a = ?a' → ?b = ?b' → ?c = ?c' → f ?a ?b ?c = f' ?a' ?b' ?c'
congr4|∀ (f f' : ?A → ?B → ?C → ?D → ?E), f = f' → ?a = ?a' → ?b = ?b' → ?c = ?c' → ?d = ?d' → f ?a ?b ?c ?d = f' ?a' ?b' ?c' ?d'
congr5|∀ (f f' : ?A → ?B → ?C → ?D → ?E → ?F), f = f' → ?a = ?a' → ?b = ?b' → ?c = ?c' → ?d = ?d' → ?e = ?e' → f ?a ?b ?c ?d ?e = f' ?a' ?b' ?c' ?d' ?e'
congr_arg2|∀ (f : ?A → ?B → ?C), ?a = ?a' → ?b = ?b' → f ?a ?b = f ?a' ?b'
congr_arg3|∀ (f : ?A → ?B → ?C → ?D), ?a = ?a' → ?b = ?b' → ?c = ?c' → f ?a ?b ?c = f ?a' ?b' ?c'
congr_arg4|∀ (f : ?A → ?B → ?C → ?D → ?E), ?a = ?a' → ?b = ?b' → ?c = ?c' → ?d = ?d' → f ?a ?b ?c ?d = f ?a' ?b' ?c' ?d'
congr_arg5|∀ (f : ?A → ?B → ?C → ?D → ?E → ?F), ?a = ?a' → ?b = ?b' → ?c = ?c' → ?d = ?d' → ?e = ?e' → f ?a ?b ?c ?d ?e = f ?a' ?b' ?c' ?d' ?e'
congr_arg|∀ (f : ?A → ?B), ?a₁ = ?a₂ → f ?a₁ = f ?a₂
congr_fun|?f = ?g → (∀ (a : ?A), ?f a = ?g a)
congr|?f₁ = ?f₂ → ?a₁ = ?a₂ → ?f₁ ?a₁ = ?f₂ ?a₂
conj_by|?A → ?A → ?A
conj_compose|∀ (f g a : ?A), conj_by f (conj_by g a) = conj_by (f * g) a
conj_id|∀ (a : ?A), conj_by 1 a = a
conj_inv_cancel|∀ (g a : ?A), conj_by g⁻¹ (conj_by g a) = a
conj_inv|∀ (g a : ?A), (conj_by g a)⁻¹ = conj_by g a⁻¹
conj_one|∀ (g : ?A), conj_by g 1 = 1
dcongr_arg2|∀ (f : Π (a : ?A), ?B a → ?F) (Ha : ?a = ?a'), eq.rec_on Ha ?b = ?b' → f ?a ?b = f ?a' ?b'
dcongr_arg3|∀ (f : Π (a : ?A) (b : ?B a), ?C a b → ?F) (Ha : ?a = ?a') (Hb : eq.rec_on Ha ?b = ?b'), cast (dcongr_arg2 ?C Ha Hb) ?c = ?c' → f ?a ?b ?c = f ?a' ?b' ?c'
dcongr_arg4|∀ (f : Π (a : ?A) (b : ?B a) (c : ?C a b), ?D a b c → ?F) (Ha : ?a = ?a') (Hb : eq.rec_on Ha ?b = ?b') (Hc : cast (dcongr_arg2 ?C Ha Hb) ?c = ?c'), cast (dcongr_arg3 ?D Ha Hb Hc) ?d = ?d' → f ?a ?b ?c ?d = f ?a' ?b' ?c' ?d'
dec_eq_of_dec_lt|Π (x y : ?A), decidable (x = y)
decidable.by_cases|(?p → ?q) → (¬?p → ?q) → ?q
decidable.by_contradiction|(¬?p → false) → ?p
decidable.cases_on|Π (n : decidable ?p), (Π (a : ?p), ?C (decidable.inl a)) → (Π (a : ¬?p), ?C (decidable.inr a)) → ?C n
decidable.em|∀ (p : Prop) [_inst_1 : decidable p], p ∨ ¬p
decidable.inl|?p → decidable ?p
decidable.inr|¬?p → decidable ?p
decidable.rec_on|Π (n : decidable ?p), (Π (a : ?p), ?C (decidable.inl a)) → (Π (a : ¬?p), ?C (decidable.inr a)) → ?C n
decidable.rec|(Π (a : ?p), ?C (decidable.inl a)) → (Π (a : ¬?p), ?C (decidable.inr a)) → (Π (n : decidable ?p), ?C n)
decidable_and|decidable (?p ∧ ?q)
decidable_ball_le|Π (n : ℕ) (P : ℕ → Prop) [_inst_1 : decidable_pred P], decidable (∀ (x : ℕ), x ≤ n → P x)
decidable_ball|Π (n : ℕ) (P : ℕ → Prop) [H : decidable_pred P], decidable (nat.ball n P)
decidable_bex_le|Π (n : ℕ) (P : ℕ → Prop) [_inst_1 : decidable_pred P], decidable (∃ (x : ℕ), x ≤ n ∧ P x)
decidable_bex|Π (n : ℕ) (P : ℕ → Prop) [H : decidable_pred P], decidable (nat.bex n P)
decidable_eq_char|Π (c₁ c₂ : char), decidable (c₁ = c₂)
decidable_eq_fun|decidable_eq (?A → ?B)
decidable_eq_inl_refl|∀ (a : ?A), ?H a a = decidable.inl (eq.refl a)
decidable_eq|Type → Type
decidable_false|decidable false
decidable_forall_eq|Π (P : ?A → Prop) (a : ?A) [H : decidable (P a)], decidable (∀ (x : ?A), x = a → P x)
decidable_iff|decidable (?p ↔ ?q)
decidable_implies|decidable (?p → ?q)
decidable_le|decidable (?a ≤ ?b)
decidable_linear_order.induction_on|Π (n : decidable_linear_order ?A), (Π (le : ?A → ?A → Prop) (le_refl : ∀ (a : ?A), le a a) (le_trans : ∀ (a b c : ?A), le a b → le b c → le a c) (le_antisymm : ∀ (a b : ?A), le a b → le b a → a = b) (lt : ?A → ?A → Prop) (le_iff_lt_or_eq : ∀ (a b : ?A), le a b ↔ lt a b ∨ a = b) (lt_irrefl : ∀ (a : ?A), ¬lt a a) (le_total : ∀ (a b : ?A), le a b ∨ le b a) (decidable_lt : decidable_rel lt), ?C (decidable_linear_order.mk le le_refl le_trans le_antisymm lt le_iff_lt_or_eq lt_irrefl le_total decidable_lt)) → ?C n
decidable_linear_order.mk|Π (le : ?A → ?A → Prop), (∀ (a : ?A), le a a) → (∀ (a b c : ?A), le a b → le b c → le a c) → (∀ (a b : ?A), le a b → le b a → a = b) → (Π (lt : ?A → ?A → Prop), (∀ (a b : ?A), le a b ↔ lt a b ∨ a = b) → (∀ (a : ?A), ¬lt a a) → (∀ (a b : ?A), le a b ∨ le b a) → decidable_rel lt → decidable_linear_order ?A)
decidable_linear_ordered_cancel_comm_monoid.mk|Π (add : ?A → ?A → ?A), (∀ (a b c : ?A), add (add a b) c = add a (add b c)) → (Π (zero : ?A), (∀ (a : ?A), add zero a = a) → (∀ (a : ?A), add a zero = a) → (∀ (a b : ?A), add a b = add b a) → (∀ (a b c : ?A), add a b = add a c → b = c) → (∀ (a b c : ?A), add a b = add c b → a = c) → (Π (le : ?A → ?A → Prop), (∀ (a : ?A), le a a) → (∀ (a b c : ?A), le a b → le b c → le a c) → (∀ (a b : ?A), le a b → le b a → a = b) → (Π (lt : ?A → ?A → Prop), (∀ (a b : ?A), lt a b → le a b) → (∀ (a b c : ?A), lt a b → le b c → lt a c) → (∀ (a b c : ?A), le a b → lt b c → lt a c) → (∀ (a : ?A), ¬lt a a) → (Π (a b : ?A), le a b → (∀ (c : ?A), le (add c a) (add c b))) → (∀ (a b c : ?A), le (add a b) (add a c) → le b c) → (Π (a b : ?A), lt a b → (∀ (c : ?A), lt (add c a) (add c b))) → (∀ (a b c : ?A), lt (add a b) (add a c) → lt b c) → (∀ (a b : ?A), le a b ↔ lt a b ∨ a = b) → (∀ (a b : ?A), le a b ∨ le b a) → decidable_rel lt → decidable_linear_ordered_cancel_comm_monoid ?A)))
decidable_linear_ordered_comm_group._trans_of_to_add_comm_group_4|Π (A : Type) [s : decidable_linear_ordered_comm_group A], add_semigroup A
decidable_linear_ordered_comm_group._trans_of_to_add_comm_group_5|Π (A : Type) [s : decidable_linear_ordered_comm_group A], add_comm_monoid A
decidable_linear_ordered_comm_group._trans_of_to_add_comm_group_9|Π (A : Type) [s : decidable_linear_ordered_comm_group A], add_group A
decidable_linear_ordered_comm_ring._trans_of_to_decidable_linear_ordered_comm_group_13|Π (A : Type) [s : decidable_linear_ordered_comm_ring A], has_lt A
decidable_linear_ordered_comm_ring._trans_of_to_decidable_linear_ordered_semiring_5|add_monoid ?A
decidable_linear_ordered_comm_ring._trans_of_to_linear_ordered_comm_ring_35|Π (A : Type) [s : decidable_linear_ordered_comm_ring A], has_lt A
decidable_linear_ordered_comm_ring.mk|Π (add : ?A → ?A → ?A), (∀ (a b c : ?A), add (add a b) c = add a (add b c)) → (Π (zero : ?A), (∀ (a : ?A), add zero a = a) → (∀ (a : ?A), add a zero = a) → (Π (neg : ?A → ?A), (∀ (a : ?A), add (neg a) a = zero) → (∀ (a b : ?A), add a b = add b a) → (Π (mul : ?A → ?A → ?A), (∀ (a b c : ?A), mul (mul a b) c = mul a (mul b c)) → (Π (one : ?A), (∀ (a : ?A), mul one a = a) → (∀ (a : ?A), mul a one = a) → (∀ (a b c : ?A), mul a (add b c) = add (mul a b) (mul a c)) → (∀ (a b c : ?A), mul (add a b) c = add (mul a c) (mul b c)) → (Π (le : ?A → ?A → Prop), (∀ (a : ?A), le a a) → (∀ (a b c : ?A), le a b → le b c → le a c) → (∀ (a b : ?A), le a b → le b a → a = b) → (Π (lt : ?A → ?A → Prop), (∀ (a b : ?A), lt a b → le a b) → (∀ (a b c : ?A), lt a b → le b c → lt a c) → (∀ (a b c : ?A), le a b → lt b c → lt a c) → (∀ (a : ?A), ¬lt a a) → (Π (a b : ?A), le a b → (∀ (c : ?A), le (add c a) (add c b))) → (Π (a b : ?A), lt a b → (∀ (c : ?A), lt (add c a) (add c b))) → zero ≠ one → (∀ (a b : ?A), le zero a → le zero b → le zero (mul a b)) → (∀ (a b : ?A), lt zero a → lt zero b → lt zero (mul a b)) → (∀ (a b : ?A), le a b ↔ lt a b ∨ a = b) → (∀ (a b : ?A), le a b ∨ le b a) → lt zero one → (∀ (a b : ?A), mul a b = mul b a) → decidable_rel lt → decidable_linear_ordered_comm_ring ?A))))))
decidable_linear_ordered_semiring._trans_of_to_decidable_linear_ordered_cancel_comm_monoid_3|Π (A : Type) [s : decidable_linear_ordered_semiring A], has_le A
decidable_linear_ordered_semiring._trans_of_to_linear_ordered_semiring_1|Π (A : Type) [s : decidable_linear_ordered_semiring A], strict_order A
decidable_lt|decidable (?a < ?b)
decidable_ne|Π (a b : ?A), decidable (a ≠ b)
decidable_not|decidable (¬?p)
decidable_or|decidable (?p ∨ ?q)
decidable_pred|(?A → Prop) → Type
decidable_rel|(?A → ?A → Prop) → Type
decidable_true|decidable true
decidable|Prop → Type₁
default|Π (A : Type) [H : inhabited A], A
dif_ctx_congr|Π (h_c : ?b ↔ ?c), (∀ (h : ?c), ?x (iff.mpr h_c h) = ?u h) → (∀ (h : ¬?c), ?y (iff.mpr (not_iff_not_of_iff h_c) h) = ?v h) → dite ?b ?x ?y = dite ?c ?u ?v
dif_ctx_simp_congr|Π (h_c : ?b ↔ ?c), (∀ (h : ?c), ?x (iff.mpr h_c h) = ?u h) → (∀ (h : ¬?c), ?y (iff.mpr (not_iff_not_of_iff h_c) h) = ?v h) → dite ?b ?x ?y = dite ?c ?u ?v
dif_neg|∀ (Hnc : ¬?c) {A : Type} {t : ?c → A} {e : ¬?c → A}, dite ?c t e = e Hnc
dif_pos|∀ (Hc : ?c) {A : Type} {t : ?c → A} {e : ¬?c → A}, dite ?c t e = t Hc
discrete_field.mk|Π (add : ?A → ?A → ?A), (∀ (a b c : ?A), add (add a b) c = add a (add b c)) → (Π (zero : ?A), (∀ (a : ?A), add zero a = a) → (∀ (a : ?A), add a zero = a) → (Π (neg : ?A → ?A), (∀ (a : ?A), add (neg a) a = zero) → (∀ (a b : ?A), add a b = add b a) → (Π (mul : ?A → ?A → ?A), (∀ (a b c : ?A), mul (mul a b) c = mul a (mul b c)) → (Π (one : ?A), (∀ (a : ?A), mul one a = a) → (∀ (a : ?A), mul a one = a) → (∀ (a b c : ?A), mul a (add b c) = add (mul a b) (mul a c)) → (∀ (a b c : ?A), mul (add a b) c = add (mul a c) (mul b c)) → (Π (inv : ?A → ?A), zero ≠ one → (∀ {a : ?A}, a ≠ zero → mul a (inv a) = one) → (∀ {a : ?A}, a ≠ zero → mul (inv a) a = one) → (∀ (a b : ?A), mul a b = mul b a) → decidable_eq ?A → inv zero = zero → discrete_field ?A)))))
discrete_field.rec|(Π (add : ?A → ?A → ?A) (add_assoc : ∀ (a b c : ?A), add (add a b) c = add a (add b c)) (zero : ?A) (zero_add : ∀ (a : ?A), add zero a = a) (add_zero : ∀ (a : ?A), add a zero = a) (neg : ?A → ?A) (add_left_inv : ∀ (a : ?A), add (neg a) a = zero) (add_comm : ∀ (a b : ?A), add a b = add b a) (mul : ?A → ?A → ?A) (mul_assoc : ∀ (a b c : ?A), mul (mul a b) c = mul a (mul b c)) (one : ?A) (one_mul : ∀ (a : ?A), mul one a = a) (mul_one : ∀ (a : ?A), mul a one = a) (left_distrib : ∀ (a b c : ?A), mul a (add b c) = add (mul a b) (mul a c)) (right_distrib : ∀ (a b c : ?A), mul (add a b) c = add (mul a c) (mul b c)) (inv : ?A → ?A) (zero_ne_one : zero ≠ one) (mul_inv_cancel : ∀ {a : ?A}, a ≠ zero → mul a (inv a) = one) (inv_mul_cancel : ∀ {a : ?A}, a ≠ zero → mul (inv a) a = one) (mul_comm : ∀ (a b : ?A), mul a b = mul b a) (has_decidable_eq : decidable_eq ?A) (inv_zero : inv zero = zero), ?C (discrete_field.mk add add_assoc zero zero_add add_zero neg add_left_inv add_comm mul mul_assoc one one_mul mul_one left_distrib right_distrib inv zero_ne_one mul_inv_cancel inv_mul_cancel mul_comm has_decidable_eq inv_zero)) → (Π (n : discrete_field ?A), ?C n)
discrete_field|Type → Type
discrete_linear_ordered_field._trans_of_to_decidable_linear_ordered_comm_ring_27|Π (A : Type) [s : discrete_linear_ordered_field A], add_semigroup A
discrete_linear_ordered_field.mk|Π (add : ?A → ?A → ?A), (∀ (a b c : ?A), add (add a b) c = add a (add b c)) → (Π (zero : ?A), (∀ (a : ?A), add zero a = a) → (∀ (a : ?A), add a zero = a) → (Π (neg : ?A → ?A), (∀ (a : ?A), add (neg a) a = zero) → (∀ (a b : ?A), add a b = add b a) → (Π (mul : ?A → ?A → ?A), (∀ (a b c : ?A), mul (mul a b) c = mul a (mul b c)) → (Π (one : ?A), (∀ (a : ?A), mul one a = a) → (∀ (a : ?A), mul a one = a) → (∀ (a b c : ?A), mul a (add b c) = add (mul a b) (mul a c)) → (∀ (a b c : ?A), mul (add a b) c = add (mul a c) (mul b c)) → (Π (le : ?A → ?A → Prop), (∀ (a : ?A), le a a) → (∀ (a b c : ?A), le a b → le b c → le a c) → (∀ (a b : ?A), le a b → le b a → a = b) → (Π (lt : ?A → ?A → Prop), (∀ (a b : ?A), lt a b → le a b) → (∀ (a b c : ?A), lt a b → le b c → lt a c) → (∀ (a b c : ?A), le a b → lt b c → lt a c) → (∀ (a : ?A), ¬lt a a) → (Π (a b : ?A), le a b → (∀ (c : ?A), le (add c a) (add c b))) → (Π (a b : ?A), lt a b → (∀ (c : ?A), lt (add c a) (add c b))) → zero ≠ one → (∀ (a b : ?A), le zero a → le zero b → le zero (mul a b)) → (∀ (a b : ?A), lt zero a → lt zero b → lt zero (mul a b)) → (∀ (a b : ?A), le a b ↔ lt a b ∨ a = b) → (∀ (a b : ?A), le a b ∨ le b a) → lt zero one → (Π (inv : ?A → ?A), (∀ {a : ?A}, a ≠ zero → mul a (inv a) = one) → (∀ {a : ?A}, a ≠ zero → mul (inv a) a = one) → (∀ (a b : ?A), mul a b = mul b a) → decidable_rel lt → inv zero = zero → discrete_linear_ordered_field ?A)))))))
distrib.cases_on|Π (n : distrib ?A), (Π (mul add : ?A → ?A → ?A) (left_distrib : ∀ (a b c : ?A), mul a (add b c) = add (mul a b) (mul a c)) (right_distrib : ∀ (a b c : ?A), mul (add a b) c = add (mul a c) (mul b c)), ?C (distrib.mk mul add left_distrib right_distrib)) → ?C n
distrib.destruct|Π (n : distrib ?A), (Π (mul add : ?A → ?A → ?A) (left_distrib : ∀ (a b c : ?A), mul a (add b c) = add (mul a b) (mul a c)) (right_distrib : ∀ (a b c : ?A), mul (add a b) c = add (mul a c) (mul b c)), ?C (distrib.mk mul add left_distrib right_distrib)) → ?C n
distrib.mk|Π (mul add : ?A → ?A → ?A), (∀ (a b c : ?A), mul a (add b c) = add (mul a b) (mul a c)) → (∀ (a b c : ?A), mul (add a b) c = add (mul a c) (mul b c)) → distrib ?A
distrib.rec_on|Π (n : distrib ?A), (Π (mul add : ?A → ?A → ?A) (left_distrib : ∀ (a b c : ?A), mul a (add b c) = add (mul a b) (mul a c)) (right_distrib : ∀ (a b c : ?A), mul (add a b) c = add (mul a c) (mul b c)), ?C (distrib.mk mul add left_distrib right_distrib)) → ?C n
distrib.rec|(Π (mul add : ?A → ?A → ?A) (left_distrib : ∀ (a b c : ?A), mul a (add b c) = add (mul a b) (mul a c)) (right_distrib : ∀ (a b c : ?A), mul (add a b) c = add (mul a c) (mul b c)), ?C (distrib.mk mul add left_distrib right_distrib)) → (Π (n : distrib ?A), ?C n)
distrib.to_has_add|Π (A : Type) [s : distrib A], has_add A
distrib.to_has_mul|Π (A : Type) [s : distrib A], has_mul A
distrib_three_right|∀ (a b c d : ?A), (a + b + c) * d = a * d + b * d + c * d
distrib|Type → Type
dite_ite_eq|∀ (c : Prop) [_inst_1 : decidable c] {A : Type} (t e : A), dite c (λ (h : c), t) (λ (h : ¬c), e) = ite c t e
dite|Π (c : Prop) [H : decidable c] {A : Type}, (c → A) → (¬c → A) → A
div_add_div_same|∀ (a b c : ?A), a / c + b / c = (a + b) / c
div_add_div|∀ (a : ?A) {b : ?A} (c : ?A) {d : ?A}, b ≠ 0 → d ≠ 0 → a / b + c / d = (a * d + b * c) / (b * d)
div_div_div_div_eq|∀ (a b c d : ?A), a / b / (c / d) = a * d / (b * c)
div_div_eq_div_mul|∀ (a b c : ?A), a / b / c = a / (b * c)
div_div_eq_mul_div|∀ (a b c : ?A), a / (b / c) = a * c / b
div_eq_mul_one_div|∀ (a b : ?A), a / b = a * (1 / b)
div_eq_one_iff_eq|∀ (a : ?A) {b : ?A}, b ≠ 0 → (a / b = 1 ↔ a = b)
div_helper|∀ (b : ?A), ?a ≠ 0 → 1 / (?a * b) * ?a = 1 / b
div_le_div_of_le_of_neg|?b ≤ ?a → ?c < 0 → ?a / ?c ≤ ?b / ?c
div_le_of_le_mul|?b > 0 → ?a ≤ ?b * ?c → ?a / ?b ≤ ?c
div_lt_of_mul_lt_of_pos|?c > 0 → ?b < ?a * ?c → ?b / ?c < ?a
div_mul_cancel|∀ (a : ?A) {b : ?A}, b ≠ 0 → a / b * b = a
div_mul_div|∀ (a b c : ?A) {d : ?A}, a / b * (c / d) = a * c / (b * d)
div_mul_eq_mul_div|∀ (a b c : ?A), b / c * a = b * a / c
div_mul_left|∀ (a : ?A) {b : ?A}, b ≠ 0 → b / (a * b) = 1 / a
div_mul_right|∀ (b : ?A), ?a ≠ 0 → ?a / (?a * b) = 1 / b
div_neg_eq_neg_div|∀ (b : ?A), ?a ≠ 0 → b / -?a = -(b / ?a)
div_one|∀ (a : ?A), a / 1 = a
div_pow|∀ (a : ?A) {b : ?A} {n : ℕ}, (a / b) ^ n = a ^ n / b ^ n
div_self|?a ≠ 0 → ?a / ?a = 1
div_sub_div_same|∀ (a b c : ?A), a / c - b / c = (a - b) / c
div_sub_div|∀ (a : ?A) {b : ?A} (c : ?A) {d : ?A}, b ≠ 0 → d ≠ 0 → a / b - c / d = (a * d - b * c) / (b * d)
div_two_add_div_four_lt|?a > 0 → ?a / 2 + ?a / 4 < ?a
div_two_lt_of_pos|?a > 0 → ?a / (1 + 1) < ?a
div_two_sub_self|∀ (a : ?A), a / 2 - a = -(a / 2)
div_zero|∀ (a : ?A), a / 0 = 0
division.def|∀ (a b : ?A), a / b = a * b⁻¹
division_ring._trans_of_to_ring_17|Π (A : Type) [s : division_ring A], add_comm_group A
division_ring.mk|Π (add : ?A → ?A → ?A), (∀ (a b c : ?A), add (add a b) c = add a (add b c)) → (Π (zero : ?A), (∀ (a : ?A), add zero a = a) → (∀ (a : ?A), add a zero = a) → (Π (neg : ?A → ?A), (∀ (a : ?A), add (neg a) a = zero) → (∀ (a b : ?A), add a b = add b a) → (Π (mul : ?A → ?A → ?A), (∀ (a b c : ?A), mul (mul a b) c = mul a (mul b c)) → (Π (one : ?A), (∀ (a : ?A), mul one a = a) → (∀ (a : ?A), mul a one = a) → (∀ (a b c : ?A), mul a (add b c) = add (mul a b) (mul a c)) → (∀ (a b c : ?A), mul (add a b) c = add (mul a c) (mul b c)) → (Π (inv : ?A → ?A), zero ≠ one → (∀ {a : ?A}, a ≠ zero → mul a (inv a) = one) → (∀ {a : ?A}, a ≠ zero → mul (inv a) a = one) → division_ring ?A)))))
division_ring.mul_ne_zero|?a ≠ 0 → ?b ≠ 0 → ?a * ?b ≠ 0
division_ring.one_div_one_div|?a ≠ 0 → 1 / (1 / ?a) = ?a
division_ring.rec|(Π (add : ?A → ?A → ?A) (add_assoc : ∀ (a b c : ?A), add (add a b) c = add a (add b c)) (zero : ?A) (zero_add : ∀ (a : ?A), add zero a = a) (add_zero : ∀ (a : ?A), add a zero = a) (neg : ?A → ?A) (add_left_inv : ∀ (a : ?A), add (neg a) a = zero) (add_comm : ∀ (a b : ?A), add a b = add b a) (mul : ?A → ?A → ?A) (mul_assoc : ∀ (a b c : ?A), mul (mul a b) c = mul a (mul b c)) (one : ?A) (one_mul : ∀ (a : ?A), mul one a = a) (mul_one : ∀ (a : ?A), mul a one = a) (left_distrib : ∀ (a b c : ?A), mul a (add b c) = add (mul a b) (mul a c)) (right_distrib : ∀ (a b c : ?A), mul (add a b) c = add (mul a c) (mul b c)) (inv : ?A → ?A) (zero_ne_one : zero ≠ one) (mul_inv_cancel : ∀ {a : ?A}, a ≠ zero → mul a (inv a) = one) (inv_mul_cancel : ∀ {a : ?A}, a ≠ zero → mul (inv a) a = one), ?C (division_ring.mk add add_assoc zero zero_add add_zero neg add_left_inv add_comm mul mul_assoc one one_mul mul_one left_distrib right_distrib inv zero_ne_one mul_inv_cancel inv_mul_cancel)) → (Π (n : division_ring ?A), ?C n)
division_ring|Type → Type
div|?A → ?A → ?A
dpair|Π (pr1 : ?A), ?B pr1 → sigma ?B
dvd.elim_left|?a ∣ ?b → (Π (c : ?A), ?b = c * ?a → ?P) → ?P
dvd.elim|?a ∣ ?b → (Π (c : ?A), ?b = ?a * c → ?P) → ?P
dvd.intro_left|?c * ?a = ?b → ?a ∣ ?b
dvd.intro|?a * ?c = ?b → ?a ∣ ?b
dvd.refl|∀ (a : ?A), a ∣ a
dvd.trans|?a ∣ ?b → ?b ∣ ?c → ?a ∣ ?c
dvd_abs_iff|∀ (a b : ?A), a ∣ abs b ↔ a ∣ b
dvd_abs_of_dvd|?a ∣ ?b → ?a ∣ abs ?b
dvd_add|?a ∣ ?b → ?a ∣ ?c → ?a ∣ ?b + ?c
dvd_mul_left|∀ (a b : ?A), a ∣ b * a
dvd_mul_right|∀ (a b : ?A), a ∣ a * b
dvd_neg_iff_dvd|∀ (a b : ?A), a ∣ -b ↔ a ∣ b
dvd_neg_of_dvd|∀ (a b : ?A), a ∣ b → a ∣ -b
dvd_of_dvd_neg|∀ (a b : ?A), a ∣ -b → a ∣ b
dvd_of_mul_dvd_mul_right|?a ≠ 0 → ?b * ?a ∣ ?c * ?a → ?b ∣ ?c
dvd_of_mul_left_dvd|?a * ?b ∣ ?c → ?b ∣ ?c
dvd_of_mul_left_eq|?c * ?a = ?b → ?a ∣ ?b
dvd_of_neg_dvd|∀ (a b : ?A), -a ∣ b → a ∣ b
dvd_sub|∀ (a b c : ?A), a ∣ b → a ∣ c → a ∣ b - c
dvd_zero|∀ (a : ?A), a ∣ 0
dvd|?A → ?A → Prop
elements_of|Π (A : Type) [h : fintype A], list A
empty.cases_on|Π (C : empty → Type) (n : empty), C n
empty.elim|Π (A : Type), empty → A
empty.rec_on|Π (C : empty → Type) (n : empty), C n
empty.rec|Π (C : empty → Type) (n : empty), C n
empty.wf|well_founded empty_relation
empty_relation|?A → ?A → Prop
empty|Type₁
eq.cases_on|?a = ?a → ?C ?a → ?C ?a
eq.drec_on|Π (h₂ : ?a = ?b), ?C ?a (eq.refl ?a) → ?C ?b h₂
eq.drec|?C ?a (eq.refl ?a) → (Π {b : ?A} (h₂ : ?a = b), ?C b h₂)
eq.id_refl|∀ (H₁ : ?a = ?a), H₁ = eq.refl ?a
eq.induction_on|?a = ?a → ?C ?a → ?C ?a
eq.irrel|∀ (H₁ H₂ : ?a = ?a'), H₁ = H₂
eq.mpr|?a = ?b → ?b → ?a
eq.mp|?a = ?b → ?a → ?b
eq.rec_on_comp|∀ (H₁ : ?a = ?b) (H₂ : ?b = ?c) (u : ?P ?a), eq.rec_on H₂ (eq.rec_on H₁ u) = eq.rec_on (eq.trans H₁ H₂) u
eq.rec_on_id|∀ (H : ?a = ?a) (b : ?B ?a), eq.rec_on H b = b
eq.rec_on_irrel|∀ (H H' : ?a = ?a') (b : ?D ?a), eq.drec_on H b = eq.drec_on H' b
eq.rec_on|?a = ?a → ?C ?a → ?C ?a
eq.rec|?C ?a → (Π {a : ?A}, ?a = a → ?C a)
eq.refl|∀ (a : ?A), a = a
eq.substr|?b = ?a → ?P ?a → ?P ?b
eq.subst|?a = ?b → ?P ?a → ?P ?b
eq.symm|?a = ?b → ?b = ?a
eq.trans|?a = ?b → ?b = ?c → ?a = ?c
eq_add_of_sub_eq'|?a - ?b = ?c → ?a = ?b + ?c
eq_add_of_sub_eq|?a - ?c = ?b → ?a = ?b + ?c
eq_bot|(∀ (b : ?A), ?a ≤ b) → ?a = ⊥
eq_div_of_mul_eq|∀ (a b : ?A) {c : ?A}, c ≠ 0 → a * c = b → a = b / c
eq_imp_trans|?a = ?b → (?b → ?c) → ?a → ?c
eq_inf|?c ≤ ?a → ?c ≤ ?b → (∀ {d : ?A}, d ≤ ?a → d ≤ ?b → d ≤ ?c) → ?c = ?a ⊓ ?b
eq_inv_iff_eq_inv|∀ (a b : ?A), a = b⁻¹ ↔ b = a⁻¹
eq_inv_of_eq_inv|?a = ?b⁻¹ → ?b = ?a⁻¹
eq_max|?a ≤ ?c → ?b ≤ ?c → (∀ {d : ?A}, ?a ≤ d → ?b ≤ d → ?c ≤ d) → ?c = max ?a ?b
eq_min|?c ≤ ?a → ?c ≤ ?b → (∀ {d : ?A}, d ≤ ?a → d ≤ ?b → d ≤ ?c) → ?c = min ?a ?b
eq_neg_iff_eq_neg|∀ (a b : ?A), a = -b ↔ b = -a
eq_neg_of_add_eq_zero|?a + ?b = 0 → ?a = -?b
eq_neg_of_eq_neg|?a = -?b → ?b = -?a
eq_of_abs_sub_eq_zero|abs (?a - ?b) = 0 → ?a = ?b
eq_of_div_eq_one|∀ (a : ?A) {b : ?A}, b ≠ 0 → a / b = 1 → a = b
eq_of_heq|?a == ?a' → ?a = ?a'
eq_of_le_of_ge|?a ≤ ?b → ?b ≤ ?a → ?a = ?b
eq_of_neg_eq_neg|-?a = -?b → ?a = ?b
eq_of_sub_eq_zero|?a - ?b = 0 → ?a = ?b
eq_one_of_inv_eq_one|∀ (a : ?A), a⁻¹ = 1 → a = 1
eq_or_lt_of_le|?a ≤ ?b → ?a = ?b ∨ ?a < ?b
eq_rec_compose|∀ (p₁ : ?B = ?C) (p₂ : ?A = ?B) (a : ?A), eq.rec (eq.rec a p₂) p₁ = eq.rec a (eq.trans p₂ p₁)
eq_rec_eq_eq_rec|eq.rec ?a₁ ?p = ?a₂ → ?a₁ = eq.rec ?a₂ (eq.symm ?p)
eq_rec_heq|∀ (H : ?a = ?a') (p : ?P ?a), eq.rec p H == p
eq_rec_to_heq|eq.rec_on ?H₁ ?p = ?p' → ?p == ?p'
eq_self_iff_true|∀ (a : ?A), a = a ↔ true
eq_sign_mul_abs|∀ (a : ?A), a = sign a * abs a
eq_sub_iff_add_eq|∀ (a b c : ?A), a = b - c ↔ a + c = b
eq_sub_of_add_eq'|?c + ?a = ?b → ?a = ?b - ?c
eq_sub_of_add_eq|?a + ?c = ?b → ?a = ?b - ?c
eq_sup|?a ≤ ?c → ?b ≤ ?c → (∀ {d : ?A}, ?a ≤ d → ?b ≤ d → ?c ≤ d) → ?c = ?a ⊔ ?b
eq_the|Π (H : exists_unique ?p) {y : ?A}, ?p y → y = the H
eq_top|(∀ (b : ?A), b ≤ ?a) → ?a = ⊤
eq_zero_of_neg_eq|-?a = ?a → ?a = 0
eq_zero_of_pow_eq_zero|?a ^ ?m = 0 → ?a = 0
eq_zero_of_sign_eq_zero|sign ?a = 0 → ?a = 0
eq_zero_of_zero_dvd|0 ∣ ?a → ?a = 0
eq_zero_or_eq_zero_of_mul_eq_zero|?a * ?b = 0 → ?a = 0 ∨ ?b = 0
eqmpr|?a = ?b → ?b → ?a
eqmp|?a = ?b → ?a → ?b
equal_f|?f = ?g → (∀ (x : ?A), ?f x = ?g x)
equiv.apply_eq_iff_eq_inverse_apply|∀ (f : equiv ?A ?B) (x : ?A) (y : ?B), equiv.fn f x = y ↔ x = equiv.fn (equiv.symm f) y
equiv.arrow_congr|equiv ?A₁ ?A₂ → equiv ?B₁ ?B₂ → equiv (?A₁ → ?B₁) (?A₂ → ?B₂)
equiv.arrow_prod_equiv_prod_arrow|Π (A : Type) (B : Type) (C : Type), equiv (C → A × B) ((C → A) × (C → B))
equiv.cases_on|Π (n : equiv ?A ?B), (Π (to_fun : ?A → ?B) (inv_fun : ?B → ?A) (left_inv : function.left_inverse inv_fun to_fun) (right_inv : function.right_inverse inv_fun to_fun), ?C (equiv.mk to_fun inv_fun left_inv right_inv)) → ?C n
equiv.comp_apply|∀ (g : equiv ?B ?C) (f : equiv ?A ?B) (x : ?A), equiv.fn (equiv.trans f g) x = equiv.fn g (equiv.fn f x)
equiv.destruct|Π (n : equiv ?A ?B), (Π (to_fun : ?A → ?B) (inv_fun : ?B → ?A) (left_inv : function.left_inverse inv_fun to_fun) (right_inv : function.right_inverse inv_fun to_fun), ?C (equiv.mk to_fun inv_fun left_inv right_inv)) → ?C n
equiv.eq_iff_eq_of_injective|function.injective ?f → (∀ (a b : ?A), ?f a = ?f b ↔ a = b)
equiv.false_arrow_equiv_unit|Π (A : Type), equiv (false → A) unit
equiv.fn|equiv ?A ?B → ?A → ?B
equiv.id_apply|∀ (x : ?A), equiv.fn (equiv.refl ?A) x = x
equiv.id|equiv ?A ?A
equiv.inv|?B → ?A
equiv.mk|Π (to_fun : ?A → ?B) (inv_fun : ?B → ?A), function.left_inverse inv_fun to_fun → function.right_inverse inv_fun to_fun → equiv ?A ?B
equiv.perm|Type → Type
equiv.prod_assoc|Π (A : Type) (B : Type) (C : Type), equiv (A × B × C) (A × (B × C))
equiv.prod_comm|Π (A : Type) (B : Type), equiv (A × B) (B × A)
equiv.prod_congr|equiv ?A₁ ?A₂ → equiv ?B₁ ?B₂ → equiv (?A₁ × ?B₁) (?A₂ × ?B₂)
equiv.prod_unit_left|Π (A : Type), equiv (unit × A) A
equiv.rec_on|Π (n : equiv ?A ?B), (Π (to_fun : ?A → ?B) (inv_fun : ?B → ?A) (left_inv : function.left_inverse inv_fun to_fun) (right_inv : function.right_inverse inv_fun to_fun), ?C (equiv.mk to_fun inv_fun left_inv right_inv)) → ?C n
equiv.rec|(Π (to_fun : ?A → ?B) (inv_fun : ?B → ?A) (left_inv : function.left_inverse inv_fun to_fun) (right_inv : function.right_inverse inv_fun to_fun), ?C (equiv.mk to_fun inv_fun left_inv right_inv)) → (Π (n : equiv ?A ?B), ?C n)
equiv.refl|Π (A : Type), equiv A A
equiv.sum_assoc|Π (A : Type) (B : Type) (C : Type), equiv (A ⊎ B ⊎ C) (A ⊎ (B ⊎ C))
equiv.sum_comm|Π (A : Type) (B : Type), equiv (A ⊎ B) (B ⊎ A)
equiv.sum_congr|equiv ?A₁ ?A₂ → equiv ?B₁ ?B₂ → equiv (?A₁ ⊎ ?B₁) (?A₂ ⊎ ?B₂)
equiv.swap_1|∀ (a_58 : Type) (a_59 : a_58) (a_60 : decidable_eq a_58) (a_61 a_62 : a_58), equiv.swap_core a_61 a_62 (equiv.swap_core a_61 a_62 a_59) = a_59
equiv.swap_2|∀ (a_68 : Type) (a_69 : a_68) (a_60 : decidable_eq a_68) (a_61 a_62 : a_68), equiv.swap_core a_61 a_62 (equiv.swap_core a_61 a_62 a_69) = a_69
equiv.swap_comm|∀ (a b : ?A), equiv.swap a b = equiv.swap b a
equiv.swap_core|?A → ?A → ?A → ?A
equiv.swap_self|∀ (a : ?A), equiv.swap a a = equiv.refl ?A
equiv.swap_swap|∀ (a b : ?A), equiv.trans (equiv.swap a b) (equiv.swap a b) = equiv.refl ?A
equiv.swap|?A → ?A → equiv.perm ?A
equiv.symm|equiv ?A ?B → equiv ?B ?A
equiv.trans|equiv ?A ?B → equiv ?B ?C → equiv ?A ?C
equiv.unit_arrow_equiv|Π (A : Type), equiv (unit → A) A
equivalence|(?B → ?B → Prop) → Prop
equiv|Type → Type → Type
eq|?A → ?A → Prop
ex_of_check_pred_eq_ff|check_pred ?p ?l = bool.ff → (∃ (w : ?A), ¬?p w)
ex_of_sig|sigma ?P → Exists ?P
exists.elim|Exists ?p → (Π (a : ?A), ?p a → ?B) → ?B
exists.intro|Π (a : ?A), ?P a → Exists ?P
exists_congr|(∀ (a : ?A), ?P a ↔ ?Q a) → (Exists ?P ↔ Exists ?Q)
exists_gt|∀ (a : ?A), ∃ (x : ?A), x > a
exists_imp_distrib|Exists ?P → ?B ↔ Π (a : ?A), ?P a → ?B
exists_imp_exists|(Π (a : ?A), ?P a → ?Q a) → Exists ?P → Exists ?Q
exists_lt|∀ (a : ?A), ∃ (x : ?A), x < a
exists_of_exists_unique|exists_unique ?p → Exists ?p
exists_p_iff_p|∀ (A : Type) [H : inhabited A] (p : Prop), (∃ (x : A), p) ↔ p
exists_unique.intro|Π (w : ?A), ?p w → (Π (y : ?A), ?p y → y = w) → exists_unique ?p
exists_unique|(?A → Prop) → Prop
false.elim|false → ?c
false.rec_on|Π (C : Type), false → C
false.rec|Π (C : Type), false → C
false_and|∀ (a : Prop), false ∧ a ↔ false
false_iff|∀ (a : Prop), false ↔ a ↔ ¬a
false_imp|∀ (a : Prop), false → a ↔ true
false_of_ne|?a ≠ ?a → false
false_or|∀ (a : Prop), false ∨ a ↔ a
false|Prop
field._trans_of_to_comm_ring_16|Π (A : Type) [s : field A], add_comm_group A
field._trans_of_to_division_ring|Π (A : Type) [s : field A], has_zero A
field.div_pow|∀ (a : ?A) {b : ?A} {n : ℕ}, b ≠ 0 → (a / b) ^ n = a ^ n / b ^ n
field.mk|Π (add : ?A → ?A → ?A), (∀ (a b c : ?A), add (add a b) c = add a (add b c)) → (Π (zero : ?A), (∀ (a : ?A), add zero a = a) → (∀ (a : ?A), add a zero = a) → (Π (neg : ?A → ?A), (∀ (a : ?A), add (neg a) a = zero) → (∀ (a b : ?A), add a b = add b a) → (Π (mul : ?A → ?A → ?A), (∀ (a b c : ?A), mul (mul a b) c = mul a (mul b c)) → (Π (one : ?A), (∀ (a : ?A), mul one a = a) → (∀ (a : ?A), mul a one = a) → (∀ (a b c : ?A), mul a (add b c) = add (mul a b) (mul a c)) → (∀ (a b c : ?A), mul (add a b) c = add (mul a c) (mul b c)) → (Π (inv : ?A → ?A), zero ≠ one → (∀ {a : ?A}, a ≠ zero → mul a (inv a) = one) → (∀ {a : ?A}, a ≠ zero → mul (inv a) a = one) → (∀ (a b : ?A), mul a b = mul b a) → field ?A)))))
field.rec_on|Π (n : field ?A), (Π (add : ?A → ?A → ?A) (add_assoc : ∀ (a b c : ?A), add (add a b) c = add a (add b c)) (zero : ?A) (zero_add : ∀ (a : ?A), add zero a = a) (add_zero : ∀ (a : ?A), add a zero = a) (neg : ?A → ?A) (add_left_inv : ∀ (a : ?A), add (neg a) a = zero) (add_comm : ∀ (a b : ?A), add a b = add b a) (mul : ?A → ?A → ?A) (mul_assoc : ∀ (a b c : ?A), mul (mul a b) c = mul a (mul b c)) (one : ?A) (one_mul : ∀ (a : ?A), mul one a = a) (mul_one : ∀ (a : ?A), mul a one = a) (left_distrib : ∀ (a b c : ?A), mul a (add b c) = add (mul a b) (mul a c)) (right_distrib : ∀ (a b c : ?A), mul (add a b) c = add (mul a c) (mul b c)) (inv : ?A → ?A) (zero_ne_one : zero ≠ one) (mul_inv_cancel : ∀ {a : ?A}, a ≠ zero → mul a (inv a) = one) (inv_mul_cancel : ∀ {a : ?A}, a ≠ zero → mul (inv a) a = one) (mul_comm : ∀ (a b : ?A), mul a b = mul b a), ?C (field.mk add add_assoc zero zero_add add_zero neg add_left_inv add_comm mul mul_assoc one one_mul mul_one left_distrib right_distrib inv zero_ne_one mul_inv_cancel inv_mul_cancel mul_comm)) → ?C n
field.rec|(Π (add : ?A → ?A → ?A) (add_assoc : ∀ (a b c : ?A), add (add a b) c = add a (add b c)) (zero : ?A) (zero_add : ∀ (a : ?A), add zero a = a) (add_zero : ∀ (a : ?A), add a zero = a) (neg : ?A → ?A) (add_left_inv : ∀ (a : ?A), add (neg a) a = zero) (add_comm : ∀ (a b : ?A), add a b = add b a) (mul : ?A → ?A → ?A) (mul_assoc : ∀ (a b c : ?A), mul (mul a b) c = mul a (mul b c)) (one : ?A) (one_mul : ∀ (a : ?A), mul one a = a) (mul_one : ∀ (a : ?A), mul a one = a) (left_distrib : ∀ (a b c : ?A), mul a (add b c) = add (mul a b) (mul a c)) (right_distrib : ∀ (a b c : ?A), mul (add a b) c = add (mul a c) (mul b c)) (inv : ?A → ?A) (zero_ne_one : zero ≠ one) (mul_inv_cancel : ∀ {a : ?A}, a ≠ zero → mul a (inv a) = one) (inv_mul_cancel : ∀ {a : ?A}, a ≠ zero → mul (inv a) a = one) (mul_comm : ∀ (a b : ?A), mul a b = mul b a), ?C (field.mk add add_assoc zero zero_add add_zero neg add_left_inv add_comm mul mul_assoc one one_mul mul_one left_distrib right_distrib inv zero_ne_one mul_inv_cancel inv_mul_cancel mul_comm)) → (Π (n : field ?A), ?C n)
field|Type → Type
fin.card_fin|∀ (n : ℕ), fintype.card (fin n) = n
fin.cases_on|Π (n : fin ?n), (Π (val : ℕ) (is_lt : val < ?n), ?C (fin.mk val is_lt)) → ?C n
fin.choice|(∀ (i : fin ?n), nonempty (?C i)) → nonempty (Π (i : fin ?n), ?C i)
fin.destruct|Π (n : fin ?n), (Π (val : ℕ) (is_lt : val < ?n), ?C (fin.mk val is_lt)) → ?C n
fin.dinj_lt|∀ (n : ℕ), list.dinj (λ (i : ℕ), i < n) fin.mk
fin.elim0|Π (i : fin 0), ?C i
fin.eq_of_veq|fin.val ?i = fin.val ?j → ?i = ?j
fin.foldl|(?B → ?A → ?B) → ?B → (Π {n : ℕ}, (fin n → ?A) → ?B)
fin.foldr|(?A → ?B → ?B) → ?B → (Π {n : ℕ}, (fin n → ?A) → ?B)
fin.lift_fun_of_inj|function.injective ?f → function.injective (fin.lift_fun ?f)
fin.lift_fun|(fin ?n → fin ?n) → fin (nat.succ ?n) → fin (nat.succ ?n)
fin.lift_succ_inj|function.injective fin.lift_succ
fin.lift_succ|fin ?n → fin (nat.succ ?n)
fin.lift_zero|fin.lift_succ 0 = 0
fin.lift|fin ?n → (Π (m : ℕ), fin (?n + m))
fin.lower_inj_apply|∀ (i : fin ?n), fin.val (fin.lower_inj ?f ?Pinj ?Pmax i) = fin.val (?f (fin.lift_succ i))
fin.lower_inj|Π (f : fin (nat.succ ?n) → fin (nat.succ ?n)), function.injective f → f fin.maxi = fin.maxi → fin ?n → fin ?n
fin.madd_inj|function.injective (fin.madd ?i)
fin.madd|fin (nat.succ ?n) → fin (nat.succ ?n) → fin (nat.succ ?n)
fin.max_lt|∀ (i j : fin ?n), max (fin.val i) (fin.val j) < ?n
fin.maxi|fin (nat.succ ?n)
fin.mem_upto|∀ (n : ℕ) (i : fin n), list.mem i (fin.upto n)
fin.minv|fin (nat.succ ?n) → fin (nat.succ ?n)
fin.mk_mod_eq|?i = fin.mk_mod ?n (fin.val ?i)
fin.mk_mod_of_lt|∀ (Plt : ?i < nat.succ ?n), fin.mk_mod ?n ?i = fin.mk ?i Plt
fin.mk_mod_zero_eq|∀ (n : ℕ), fin.mk_mod n 0 = 0
fin.mk_mod|Π (n : ℕ), ℕ → fin (nat.succ n)
fin.mk_pred|Π (i : ℕ), nat.succ i < nat.succ ?n → fin ?n
fin.mk_succ_ne_zero|fin.mk (nat.succ ?i) ?P ≠ 0
fin.mk|Π (val : ℕ), val < ?n → fin ?n
fin.nodup_upto|∀ (n : ℕ), list.nodup (fin.upto n)
fin.pred_zero|fin.pred (fin.zero ?n) = fin.zero ?n
fin.pred|fin ?n → fin ?n
fin.rec_on|Π (n : fin ?n), (Π (val : ℕ) (is_lt : val < ?n), ?C (fin.mk val is_lt)) → ?C n
fin.rec|(Π (val : ℕ) (is_lt : val < ?n), ?C (fin.mk val is_lt)) → (Π (n : fin ?n), ?C n)
fin.succ_max|fin.succ fin.maxi = fin.maxi
fin.succ|fin ?n → fin (nat.succ ?n)
fin.upto_step|fin.upto (nat.succ ?n) = list.append (list.map fin.succ (fin.upto ?n)) (list.cons 0 list.nil)
fin.upto_succ|∀ (n : ℕ), fin.upto (nat.succ n) = list.cons fin.maxi (list.map fin.lift_succ (fin.upto n))
fin.upto_zero|fin.upto 0 = list.nil
fin.upto|Π (n : ℕ), list (fin n)
fin.val_inj|fin.val ?i = fin.val ?j → ?i = ?j
fin.val_lift|∀ (i : fin ?n) (m : ℕ), fin.val i = fin.val (fin.lift i m)
fin.val_lt|∀ (i : fin ?n), fin.val i < ?n
fin.val_madd|∀ (i j : fin (nat.succ ?n)), fin.val (fin.madd i j) = (fin.val i + fin.val j) % nat.succ ?n
fin.val_mk|∀ (n i : ℕ) (Plt : i < n), fin.val (fin.mk i Plt) = i
fin.val_mod|∀ (i : fin (nat.succ ?n)), fin.val i % nat.succ ?n = fin.val i
fin.val_pred|∀ (i : fin ?n), fin.val (fin.pred i) = nat.pred (fin.val i)
fin.val_succ|∀ (i : fin ?n), fin.val (fin.succ i) = nat.succ (fin.val i)
fin.val_zero|∀ (n : ℕ), fin.val 0 = 0
fin.veq_of_eq|?i = ?j → fin.val ?i = fin.val ?j
fin.zero_madd|∀ (i : fin (nat.succ ?n)), fin.madd 0 i = i
fin.zero|Π (n : ℕ), fin (nat.succ n)
find_discr|(?A → ?B) → (?A → ?B) → list ?A → option ?A
finset.Prod_empty|∀ (f : ?A → ?B), finset.Prod finset.empty f = 1
finset.Prod_eq_of_bij_on|∀ (f : ?C → ?B) {g : ?A → ?C}, set.bij_on g (finset.to_set ?s) (finset.to_set ?t) → finset.Prod ?t f = finset.Prod ?s (λ (i : ?A), f (g i))
finset.Prod_semigroup.Prod_semigroup_singleton|∀ (dflt : ?B) (f : ?A → ?B) (a : ?A), finset.Prod_semigroup.Prod_semigroup dflt (finset.insert a finset.empty) f = f a
finset.Prod|finset ?A → (?A → ?B) → ?B
finset.Sum_insert_of_mem|∀ (f : ?A → ?B) {a : ?A} {s : finset ?A}, finset.mem a s → finset.Sum (finset.insert a s) f = finset.Sum s f
finset.Sum_zero|∀ (s : finset ?A), finset.Sum s (λ (x : ?A), 0) = 0
finset.Sum|finset ?A → (?A → ?B) → ?B
finset.Union_empty|∀ (f : ?A → finset ?B), finset.Union finset.empty f = finset.empty
finset.Union_ext|(∀ (x : ?A), finset.mem x ?s → ?f x = ?g x) → finset.Union ?s ?f = finset.Union ?s ?g
finset.Unionl_empty|∀ (l : list ?A), finset.Unionl l (λ (x : ?A), finset.empty) = finset.empty
finset.Unionl|list ?A → (?A → finset ?B) → finset ?B
finset.Union|finset ?A → (?A → finset ?B) → finset ?B
finset.all_empty|∀ (p : ?A → Prop), finset.all finset.empty p = true
finset.all|finset ?A → (?A → Prop) → Prop
finset.any_iff_exists|∀ (p : ?A → Prop) (s : finset ?A), finset.any s p ↔ ∃ (a : ?A), finset.mem a s ∧ p a
finset.any|finset ?A → (?A → Prop) → Prop
finset.card_image_eq_of_inj_on|set.inj_on ?f (finset.to_set ?s) → finset.card (finset.image ?f ?s) = finset.card ?s
finset.card_le_of_inj_on|∀ (a : finset ?A) (b : finset ?B), (∃ (f : ?A → ?B), set.inj_on f (finset.to_set a) ∧ finset.subset (finset.image f a) b) → finset.card a ≤ finset.card b
finset.card_union_of_disjoint|finset.inter ?s₁ ?s₂ = finset.empty → finset.card (finset.union ?s₁ ?s₂) = finset.card ?s₁ + finset.card ?s₂
finset.card|finset ?A → ℕ
finset.compl|finset ?A → finset ?A
finset.decidable_bounded_exists|Π (s : finset ?A) (p : ?A → Prop) [h : decidable_pred p], decidable (∃ ⦃x : ?A⦄, set.mem x (finset.to_set s) ∧ p x)
finset.diff|finset ?A → finset ?A → finset ?A
finset.disjoint.comm|finset.disjoint ?s₁ ?s₂ → finset.disjoint ?s₂ ?s₁
finset.disjoint.intro|(∀ {x : ?A}, finset.mem x ?s₁ → finset.mem x ?s₂ → false) → finset.disjoint ?s₁ ?s₂
finset.disjoint_of_inter_eq_empty|finset.inter ?s₁ ?s₂ = finset.empty → finset.disjoint ?s₁ ?s₂
finset.disjoint|finset ?A → finset ?A → Prop
finset.empty_union|∀ (s : finset ?A), finset.union finset.empty s = s
finset.empty|finset ?A
finset.eq_eq_to_set_eq|∀ (s t : finset ?A), s = t = (finset.to_set s = finset.to_set t)
finset.eq_or_mem_of_mem_insert|finset.mem ?x (finset.insert ?a ?s) → ?x = ?a ∨ finset.mem ?x ?s
finset.erase_empty|∀ (a : ?A), finset.erase a finset.empty = finset.empty
finset.erase|?A → finset ?A → finset ?A
finset.exists_mem_insert_eq|∀ (a : ?A) (s : finset ?A) (P : ?A → Prop), (∃ (x : ?A), finset.mem x (finset.insert a s) ∧ P x) = (P a ∨ ∃ (x : ?A), finset.mem x s ∧ P x)
finset.exists_of_any|finset.any ?s ?p → (∃ (a : ?A), finset.mem a ?s ∧ ?p a)
finset.ext|(∀ (a : ?A), finset.mem a ?s₁ ↔ finset.mem a ?s₂) → ?s₁ = ?s₂
finset.forall_mem_empty_eq|∀ (P : ?A → Prop), (∀ (x : ?A), finset.mem x finset.empty → P x) = true
finset.image|(?A → ?B) → finset ?A → finset ?B
finset.inj_on_of_card_image_eq|finset.card (finset.image ?f ?s) = finset.card ?s → set.inj_on ?f (finset.to_set ?s)
finset.inj_on_to_set|∀ (f : ?A → ?B) (s : finset ?A), set.inj_on f (finset.to_set s) = set.inj_on f (finset.to_set s)
finset.insert|?A → finset ?A → finset ?A
finset.inter_eq_empty_of_disjoint|finset.disjoint ?s₁ ?s₂ → finset.inter ?s₁ ?s₂ = finset.empty
finset.inter|finset ?A → finset ?A → finset ?A
finset.mem_empty_iff|∀ (x : ?A), finset.mem x finset.empty ↔ false
finset.mem_sep_eq|∀ (p : ?A → Prop) [decp : decidable_pred p] (s : finset ?A) {x : ?A}, finset.mem x (finset.sep p s) = (finset.mem x s ∧ p x)
finset.mem|?A → finset ?A → Prop
finset.partition.binary_Union|∀ (f : ?A → finset ?B) {P : ?A → Prop} [decP : decidable_pred P] {s : finset ?A}, finset.Union s f = finset.union (finset.Union (finset.sep P s) f) (finset.Union (finset.sep (λ (a : ?A), ¬P a) s) f)
finset.partition.binary_union|∀ (P : ?A → Prop) [decP : decidable_pred P] {S : finset ?A}, S = finset.union (finset.sep P S) (finset.sep (λ (a : ?A), ¬P a) S)
finset.partition.disjoint_sets_sep_of_disjoint_sets|finset.partition.disjoint_sets ?S → finset.partition.disjoint_sets (finset.sep ?P ?S)
finset.partition.disjoint_sets|finset (finset ?A) → Prop
finset.partition.equiv_class_disjoint|∀ (f : finset.partition) (a1 a2 : finset ?A), finset.mem a1 (finset.partition.equiv_classes f) → finset.mem a2 (finset.partition.equiv_classes f) → a1 ≠ a2 → finset.inter a1 a2 = finset.empty
finset.partition.mk|Π (set : finset ?A) (part : ?A → finset ?A), finset.is_partition part → set = finset.Union set part → finset.partition
finset.prio|num
finset.product_empty|∀ (s : finset ?A), finset.product s finset.empty = finset.empty
finset.sep|Π (p : ?A → Prop) [decp : decidable_pred p], finset ?A → finset ?A
finset.subset_of_mem_powerset|finset.mem ?s (finset.powerset ?t) → finset.subset ?s ?t
finset.subset|finset ?A → finset ?A → Prop
finset.to_set.inj|finset.to_set ?s₁ = finset.to_set ?s₂ → ?s₁ = ?s₂
finset.to_set|finset ?A → set ?A
finset.ts|finset ?A → set ?A
finset.union_empty|∀ (s : finset ?A), finset.union s finset.empty = s
finset.union|finset ?A → finset ?A → finset ?A
finset.univ|finset ?A
finset.upto|ℕ → finset ℕ
finset|Type → Type
fintype.card|Π (A : Type) [finA : fintype A], ℕ
fintype.mk|Π (elems : list ?A), list.nodup elems → (∀ (a : ?A), list.mem a elems) → fintype ?A
fintype.no_confusion_type|Type → fintype ?A → fintype ?A → Type
fintype.rec|(Π (elems : list ?A) (unique : list.nodup elems) (complete : ∀ (a : ?A), list.mem a elems), ?C (fintype.mk elems unique complete)) → (Π (n : fintype ?A), ?C n)
fintype.univ_of_card_eq_univ|finset.card ?s = fintype.card ?A → ?s = finset.univ
fintype_bool|fintype bool
fintype_product|fintype (?A × ?B)
fintype_unit|fintype unit
fintype|Type → Type
fin|ℕ → Type₁
fn.measurable|Π (A : Type) (B : A → Type), measurable (Π (x : A), B x)
forall_congr|(∀ (a : ?A), ?P a ↔ ?Q a) → ((Π (a : ?A), ?P a) ↔ Π (a : ?A), ?Q a)
four_pos|4 > 0
function.app|(Π (x : ?A), ?B x) → (Π (x : ?A), ?B x)
function.bijective_id|function.bijective id
function.bijective|(?A → ?B) → Prop
function.comp|(?B → ?C) → (?A → ?B) → ?A → ?C
function.equiv.is_equivalence|∀ (A : Type) (B : A → Type), equivalence function.equiv
function.injective_comp|function.injective ?g → function.injective ?f → function.injective (function.comp ?g ?f)
function.injective_of_has_left_inverse|function.has_left_inverse ?f → function.injective ?f
function.injective|(?A → ?B) → Prop
function.left_inverse_of_surjective_of_right_inverse|function.surjective ?f → function.right_inverse ?f ?g → function.left_inverse ?f ?g
function.right_inverse_of_injective_of_left_inverse|function.injective ?f → function.left_inverse ?f ?g → function.right_inverse ?f ?g
function.surjective_id|function.surjective id
function.surjective|(?A → ?B) → Prop
function.swap|(Π (x : ?A) (y : ?B), ?C x y) → (Π (y : ?B) (x : ?A), ?C x y)
function.uncurry|(?A → ?B → ?C) → ?A × ?B → ?C
funext|(∀ (x : ?A), ?f₁ x = ?f₂ x) → ?f₁ = ?f₂
ge.trans|?a ≥ ?b → ?b ≥ ?c → ?a ≥ ?c
ge_iff_of_strictly_decreasing|∀ (a₁ a₂ : ?A), strictly_decreasing ?f → (?f a₁ ≥ ?f a₂ ↔ a₁ ≤ a₂)
ge_of_forall_ge_sub|(∀ (ε : ?A), ε > 0 → ?a ≥ ?b - ε) → ?a ≥ ?b
ge|?A → ?A → Prop
gpow_add|∀ (a : ?A) (i j : ℤ), gpow a (i + j) = gpow a i * gpow a j
gpow_comm|∀ (a : ?A) (i j : ℤ), gpow a i * gpow a j = gpow a j * gpow a i
gpow|?A → ℤ → ?A
group._trans_of_to_left_cancel_semigroup_1|semigroup ?A
group._trans_of_to_left_cancel_semigroup|has_mul ?A
group._trans_of_to_monoid_1|Π (A : Type) [s : group A], has_mul A
group._trans_of_to_monoid_2|Π (A : Type) [s : group A], semigroup A
group._trans_of_to_monoid|Π (A : Type) [s : group A], has_one A
group._trans_of_to_right_cancel_semigroup_1|semigroup ?A
group._trans_of_to_right_cancel_semigroup|has_mul ?A
group.cases_on|Π (n : group ?A), (Π (mul : ?A → ?A → ?A) (mul_assoc : ∀ (a b c : ?A), mul (mul a b) c = mul a (mul b c)) (one : ?A) (one_mul : ∀ (a : ?A), mul one a = a) (mul_one : ∀ (a : ?A), mul a one = a) (inv : ?A → ?A) (mul_left_inv : ∀ (a : ?A), mul (inv a) a = one), ?C (group.mk mul mul_assoc one one_mul mul_one inv mul_left_inv)) → ?C n
group.destruct|Π (n : group ?A), (Π (mul : ?A → ?A → ?A) (mul_assoc : ∀ (a b c : ?A), mul (mul a b) c = mul a (mul b c)) (one : ?A) (one_mul : ∀ (a : ?A), mul one a = a) (mul_one : ∀ (a : ?A), mul a one = a) (inv : ?A → ?A) (mul_left_inv : ∀ (a : ?A), mul (inv a) a = one), ?C (group.mk mul mul_assoc one one_mul mul_one inv mul_left_inv)) → ?C n
group.induction_on|Π (n : group ?A), (Π (mul : ?A → ?A → ?A) (mul_assoc : ∀ (a b c : ?A), mul (mul a b) c = mul a (mul b c)) (one : ?A) (one_mul : ∀ (a : ?A), mul one a = a) (mul_one : ∀ (a : ?A), mul a one = a) (inv : ?A → ?A) (mul_left_inv : ∀ (a : ?A), mul (inv a) a = one), ?C (group.mk mul mul_assoc one one_mul mul_one inv mul_left_inv)) → ?C n
group.mk|Π (mul : ?A → ?A → ?A), (∀ (a b c : ?A), mul (mul a b) c = mul a (mul b c)) → (Π (one : ?A), (∀ (a : ?A), mul one a = a) → (∀ (a : ?A), mul a one = a) → (Π (inv : ?A → ?A), (∀ (a : ?A), mul (inv a) a = one) → group ?A))
group.no_confusion_type|Type → group ?A → group ?A → Type
group.no_confusion|?v1 = ?v2 → group.no_confusion_type ?P ?v1 ?v2
group.rec_on|Π (n : group ?A), (Π (mul : ?A → ?A → ?A) (mul_assoc : ∀ (a b c : ?A), mul (mul a b) c = mul a (mul b c)) (one : ?A) (one_mul : ∀ (a : ?A), mul one a = a) (mul_one : ∀ (a : ?A), mul a one = a) (inv : ?A → ?A) (mul_left_inv : ∀ (a : ?A), mul (inv a) a = one), ?C (group.mk mul mul_assoc one one_mul mul_one inv mul_left_inv)) → ?C n
group.rec|(Π (mul : ?A → ?A → ?A) (mul_assoc : ∀ (a b c : ?A), mul (mul a b) c = mul a (mul b c)) (one : ?A) (one_mul : ∀ (a : ?A), mul one a = a) (mul_one : ∀ (a : ?A), mul a one = a) (inv : ?A → ?A) (mul_left_inv : ∀ (a : ?A), mul (inv a) a = one), ?C (group.mk mul mul_assoc one one_mul mul_one inv mul_left_inv)) → (Π (n : group ?A), ?C n)
group.to_has_inv|Π (A : Type) [s : group A], has_inv A
group.to_left_cancel_semigroup|left_cancel_semigroup ?A
group.to_monoid|Π (A : Type) [s : group A], monoid A
group.to_right_cancel_semigroup|right_cancel_semigroup ?A
group_of_add_group|Π (A : Type) [G : add_group A], group A
group|Type → Type
gt.trans|?a > ?b → ?b > ?c → ?a > ?c
gt_iff_of_strictly_decreasing|∀ (a₁ a₂ : ?A), strictly_decreasing ?f → (?f a₁ > ?f a₂ ↔ a₁ < a₂)
gt_of_ge_of_gt|?a ≥ ?b → ?b > ?c → ?a > ?c
gt_of_gt_of_ge|?a > ?b → ?b ≥ ?c → ?a > ?c
gt_of_mul_lt_mul_neg_left|?c * ?a < ?c * ?b → ?c ≤ 0 → ?a > ?b
gt|?A → ?A → Prop
has_add.cases_on|Π (n : has_add ?A), (Π (add : ?A → ?A → ?A), ?C (has_add.mk add)) → ?C n
has_add.destruct|Π (n : has_add ?A), (Π (add : ?A → ?A → ?A), ?C (has_add.mk add)) → ?C n
has_add.mk|(?A → ?A → ?A) → has_add ?A
has_add.rec_on|Π (n : has_add ?A), (Π (add : ?A → ?A → ?A), ?C (has_add.mk add)) → ?C n
has_add.rec|(Π (add : ?A → ?A → ?A), ?C (has_add.mk add)) → (Π (n : has_add ?A), ?C n)
has_add|Type → Type
has_decidable_eq|decidable (?a = ?b)
has_div.destruct|Π (n : has_div ?A), (Π (div : ?A → ?A → ?A), ?C (has_div.mk div)) → ?C n
has_div.mk|(?A → ?A → ?A) → has_div ?A
has_div.rec_on|Π (n : has_div ?A), (Π (div : ?A → ?A → ?A), ?C (has_div.mk div)) → ?C n
has_div.rec|(Π (div : ?A → ?A → ?A), ?C (has_div.mk div)) → (Π (n : has_div ?A), ?C n)
has_div|Type → Type
has_dvd.cases_on|Π (n : has_dvd ?A), (Π (dvd : ?A → ?A → Prop), ?C (has_dvd.mk dvd)) → ?C n
has_dvd.destruct|Π (n : has_dvd ?A), (Π (dvd : ?A → ?A → Prop), ?C (has_dvd.mk dvd)) → ?C n
has_dvd.mk|(?A → ?A → Prop) → has_dvd ?A
has_dvd.rec_on|Π (n : has_dvd ?A), (Π (dvd : ?A → ?A → Prop), ?C (has_dvd.mk dvd)) → ?C n
has_dvd.rec|(Π (dvd : ?A → ?A → Prop), ?C (has_dvd.mk dvd)) → (Π (n : has_dvd ?A), ?C n)
has_dvd|Type → Type
has_inv.destruct|Π (n : has_inv ?A), (Π (inv : ?A → ?A), ?C (has_inv.mk inv)) → ?C n
has_inv.mk|(?A → ?A) → has_inv ?A
has_inv.no_confusion_type|Type → has_inv ?A → has_inv ?A → Type
has_inv.rec_on|Π (n : has_inv ?A), (Π (inv : ?A → ?A), ?C (has_inv.mk inv)) → ?C n
has_inv.rec|(Π (inv : ?A → ?A), ?C (has_inv.mk inv)) → (Π (n : has_inv ?A), ?C n)
has_inv|Type → Type
has_le.cases_on|Π (n : has_le ?A), (Π (le : ?A → ?A → Prop), ?C (has_le.mk le)) → ?C n
has_le.destruct|Π (n : has_le ?A), (Π (le : ?A → ?A → Prop), ?C (has_le.mk le)) → ?C n
has_le.mk|(?A → ?A → Prop) → has_le ?A
has_le.rec_on|Π (n : has_le ?A), (Π (le : ?A → ?A → Prop), ?C (has_le.mk le)) → ?C n
has_le.rec|(Π (le : ?A → ?A → Prop), ?C (has_le.mk le)) → (Π (n : has_le ?A), ?C n)
has_le|Type → Type
has_lt.cases_on|Π (n : has_lt ?A), (Π (lt : ?A → ?A → Prop), ?C (has_lt.mk lt)) → ?C n
has_lt.destruct|Π (n : has_lt ?A), (Π (lt : ?A → ?A → Prop), ?C (has_lt.mk lt)) → ?C n
has_lt.mk|(?A → ?A → Prop) → has_lt ?A
has_lt.rec_on|Π (n : has_lt ?A), (Π (lt : ?A → ?A → Prop), ?C (has_lt.mk lt)) → ?C n
has_lt.rec|(Π (lt : ?A → ?A → Prop), ?C (has_lt.mk lt)) → (Π (n : has_lt ?A), ?C n)
has_lt|Type → Type
has_mod.cases_on|Π (n : has_mod ?A), (Π (mod : ?A → ?A → ?A), ?C (has_mod.mk mod)) → ?C n
has_mod.destruct|Π (n : has_mod ?A), (Π (mod : ?A → ?A → ?A), ?C (has_mod.mk mod)) → ?C n
has_mod.mk|(?A → ?A → ?A) → has_mod ?A
has_mod.rec_on|Π (n : has_mod ?A), (Π (mod : ?A → ?A → ?A), ?C (has_mod.mk mod)) → ?C n
has_mod.rec|(Π (mod : ?A → ?A → ?A), ?C (has_mod.mk mod)) → (Π (n : has_mod ?A), ?C n)
has_mod|Type → Type
has_mul.cases_on|Π (n : has_mul ?A), (Π (mul : ?A → ?A → ?A), ?C (has_mul.mk mul)) → ?C n
has_mul.destruct|Π (n : has_mul ?A), (Π (mul : ?A → ?A → ?A), ?C (has_mul.mk mul)) → ?C n
has_mul.mk|(?A → ?A → ?A) → has_mul ?A
has_mul.no_confusion_type|Type → has_mul ?A → has_mul ?A → Type
has_mul.rec_on|Π (n : has_mul ?A), (Π (mul : ?A → ?A → ?A), ?C (has_mul.mk mul)) → ?C n
has_mul.rec|(Π (mul : ?A → ?A → ?A), ?C (has_mul.mk mul)) → (Π (n : has_mul ?A), ?C n)
has_mul|Type → Type
has_neg.cases_on|Π (n : has_neg ?A), (Π (neg : ?A → ?A), ?C (has_neg.mk neg)) → ?C n
has_neg.destruct|Π (n : has_neg ?A), (Π (neg : ?A → ?A), ?C (has_neg.mk neg)) → ?C n
has_neg.mk|(?A → ?A) → has_neg ?A
has_neg.rec_on|Π (n : has_neg ?A), (Π (neg : ?A → ?A), ?C (has_neg.mk neg)) → ?C n
has_neg.rec|(Π (neg : ?A → ?A), ?C (has_neg.mk neg)) → (Π (n : has_neg ?A), ?C n)
has_neg|Type → Type
has_one.cases_on|Π (n : has_one ?A), (Π (one : ?A), ?C (has_one.mk one)) → ?C n
has_one.destruct|Π (n : has_one ?A), (Π (one : ?A), ?C (has_one.mk one)) → ?C n
has_one.mk|?A → has_one ?A
has_one.rec_on|Π (n : has_one ?A), (Π (one : ?A), ?C (has_one.mk one)) → ?C n
has_one.rec|(Π (one : ?A), ?C (has_one.mk one)) → (Π (n : has_one ?A), ?C n)
has_one|Type → Type
has_pow_int.destruct|Π (n : has_pow_int ?A), (Π (pow_int : ?A → ℤ → ?A), ?C (has_pow_int.mk pow_int)) → ?C n
has_pow_int.mk|(?A → ℤ → ?A) → has_pow_int ?A
has_pow_int.rec|(Π (pow_int : ?A → ℤ → ?A), ?C (has_pow_int.mk pow_int)) → (Π (n : has_pow_int ?A), ?C n)
has_pow_int|Type → Type
has_pow_nat.cases_on|Π (n : has_pow_nat ?A), (Π (pow_nat : ?A → ℕ → ?A), ?C (has_pow_nat.mk pow_nat)) → ?C n
has_pow_nat.mk|(?A → ℕ → ?A) → has_pow_nat ?A
has_pow_nat.rec|(Π (pow_nat : ?A → ℕ → ?A), ?C (has_pow_nat.mk pow_nat)) → (Π (n : has_pow_nat ?A), ?C n)
has_pow_nat|Type → Type
has_sub.cases_on|Π (n : has_sub ?A), (Π (sub : ?A → ?A → ?A), ?C (has_sub.mk sub)) → ?C n
has_sub.mk|(?A → ?A → ?A) → has_sub ?A
has_sub.rec_on|Π (n : has_sub ?A), (Π (sub : ?A → ?A → ?A), ?C (has_sub.mk sub)) → ?C n
has_sub.rec|(Π (sub : ?A → ?A → ?A), ?C (has_sub.mk sub)) → (Π (n : has_sub ?A), ?C n)
has_sub|Type → Type
has_zero.destruct|Π (n : has_zero ?A), (Π (zero : ?A), ?C (has_zero.mk zero)) → ?C n
has_zero.mk|?A → has_zero ?A
has_zero.no_confusion_type|Type → has_zero ?A → has_zero ?A → Type
has_zero.rec_on|Π (n : has_zero ?A), (Π (zero : ?A), ?C (has_zero.mk zero)) → ?C n
has_zero.rec|(Π (zero : ?A), ?C (has_zero.mk zero)) → (Π (n : has_zero ?A), ?C n)
has_zero|Type → Type
hcongr_arg2|∀ (f : Π (a : ?A) (b : ?B a), ?C a b), ?a = ?a' → ?b == ?b' → f ?a ?b == f ?a' ?b'
hcongr_arg3|∀ (f : Π (a : ?A) (b : ?B a) (c : ?C a b), ?D a b c), ?a = ?a' → ?b == ?b' → ?c == ?c' → f ?a ?b ?c == f ?a' ?b' ?c'
hcongr_arg4|∀ (f : Π (a : ?A) (b : ?B a) (c : ?C a b) (d : ?D a b c), ?E a b c d), ?a = ?a' → ?b == ?b' → ?c == ?c' → ?d == ?d' → f ?a ?b ?c ?d == f ?a' ?b' ?c' ?d'
hcongr_arg|∀ (f : Π (x : ?A), ?P x) {a b : ?A}, a = b → f a == f b
hcongr_fun|∀ (a : ?A), ?f == ?f' → ?P = ?P' → ?f a == ?f' a
hcongr|?f == ?f' → ?P == ?P' → ?a == ?a' → ?f ?a == ?f' ?a'
hdcongr_arg3|∀ (f : Π (a : ?A) (b : ?B a), ?C a b → ?F) (Ha : ?a = ?a') (Hb : ?b == ?b'), cast (eq_of_heq (hcongr_arg2 ?C Ha Hb)) ?c = ?c' → f ?a ?b ?c = f ?a' ?b' ?c'
hddcongr_arg4|∀ (f : Π (a : ?A) (b : ?B a) (c : ?C a b), ?D a b c → ?F) (Ha : ?a = ?a') (Hb : ?b == ?b') (Hc : cast (eq_of_heq (hcongr_arg2 ?C Ha Hb)) ?c = ?c'), cast (hdcongr_arg3 ?D Ha Hb Hc) ?d = ?d' → f ?a ?b ?c ?d = f ?a' ?b' ?c' ?d'
heq.cases_on|?a == ?a → ?C ?A ?a → ?C ?B ?a
heq.drec_on|Π (H₁ : ?a == ?b), ?C ?A ?a (heq.refl ?a) → ?C ?B ?b H₁
heq.elim|?a == ?b → ?P ?a → ?P ?b
heq.induction_on|?a == ?a → ?C ?A ?a → ?C ?B ?a
heq.rec_on|?a == ?a → ?C ?A ?a → ?C ?B ?a
heq.rec|?C ?A ?a → (Π {B : Type} {a : B}, ?a == a → ?C B a)
heq.refl|∀ (a : ?A), a == a
heq.subst|?a == ?b → ?P ?A ?a → ?P ?B ?b
heq.symm|?a == ?b → ?b == ?a
heq.to_cast_eq|∀ (H : ?a == ?b), cast (type_eq_of_heq H) ?a = ?b
heq.trans|?a == ?b → ?b == ?c → ?a == ?c
heq_of_eq_of_heq|?a = ?a' → ?a' == ?b → ?a == ?b
heq_of_eq|?a = ?a' → ?a == ?a'
heq_of_heq_of_eq|?a == ?b → ?b = ?b' → ?a == ?b'
heq_self_iff_true|∀ (a : ?A), a == a ↔ true
heq|?A → (Π {B : Type}, B → Prop)
hfunext|(∀ (a : ?A), ?f a == ?g a) → ?f == ?g
hhdcongr_arg4|∀ (f : Π (a : ?A) (b : ?B a) (c : ?C a b), ?D a b c → ?F) (Ha : ?a = ?a') (Hb : ?b == ?b') (Hc : ?c == ?c'), cast (dcongr_arg3 ?D Ha (eq.trans (eq.rec_on_irrel_arg Ha (type_eq_of_heq Hb) ?b) (heq.to_cast_eq Hb)) (eq.trans (eq.rec_on_irrel_arg (dcongr_arg2 ?C Ha (eq.trans (eq.rec_on_irrel_arg Ha (type_eq_of_heq Hb) ?b) (heq.to_cast_eq Hb))) (type_eq_of_heq Hc) ?c) (heq.to_cast_eq Hc))) ?d = ?d' → f ?a ?b ?c ?d = f ?a' ?b' ?c' ?d'
hproof_irrel|?a = ?b → (∀ (H₁ : ?a) (H₂ : ?b), H₁ == H₂)
id.def|∀ (a : ?A), id a = a
id|?A → ?A
if_congr|(?b ↔ ?c) → ?x = ?u → ?y = ?v → ite ?b ?x ?y = ite ?c ?u ?v
if_ctx_congr|(?b ↔ ?c) → (?c → ?x = ?u) → (¬?c → ?y = ?v) → ite ?b ?x ?y = ite ?c ?u ?v
if_ctx_simp_congr_prop|Π (h_c : ?b ↔ ?c), (?c → (?x ↔ ?u)) → (¬?c → (?y ↔ ?v)) → (ite ?b ?x ?y ↔ ite ?c ?u ?v)
if_false|∀ (t e : ?A), ite false t e = e
if_neg|¬?c → (∀ {A : Type} {t e : A}, ite ?c t e = e)
if_pos|?c → (∀ {A : Type} {t e : A}, ite ?c t e = t)
if_t_t|∀ (c : Prop) [H : decidable c] {A : Type} (t : A), ite c t t = t
if_true|∀ (t e : ?A), ite true t e = t
iff.comm|?a ↔ ?b ↔ (?b ↔ ?a)
iff.def|(?a ↔ ?b) = ((?a → ?b) ∧ (?b → ?a))
iff.elim|((?a → ?b) → (?b → ?a) → ?c) → (?a ↔ ?b) → ?c
iff.intro|(?a → ?b) → (?b → ?a) → (?a ↔ ?b)
iff.mpr|(?a ↔ ?b) → ?b → ?a
iff.mp|(?a ↔ ?b) → ?a → ?b
iff.of_eq|?a = ?b → (?a ↔ ?b)
iff.refl|∀ (a : Prop), a ↔ a
iff.rfl|?a ↔ ?a
iff.symm|(?a ↔ ?b) → (?b ↔ ?a)
iff.trans|(?a ↔ ?b) → (?b ↔ ?c) → (?a ↔ ?c)
iff_congr|(?a ↔ ?c) → (?b ↔ ?d) → (?a ↔ ?b ↔ (?c ↔ ?d))
iff_false|∀ (a : Prop), a ↔ false ↔ ¬a
iff_self|∀ (a : Prop), a ↔ a ↔ true
iff_subst|(?a ↔ ?b) → ?P ?a → ?P ?b
iff_true|∀ (a : Prop), a ↔ true ↔ a
iff|Prop → Prop → Prop
imp.id|?a → ?a
imp.intro|?a → ?b → ?a
imp.left|(?a → ?b) → (?b → ?c) → ?a → ?c
imp.mp|?a → (?a → ?b) → ?b
imp.syl|(?a → ?b) → (?c → ?a) → ?c → ?b
imp_congr|(?a ↔ ?c) → (?b ↔ ?d) → (?a → ?b ↔ ?c → ?d)
imp_false|∀ (a : Prop), a → false ↔ ¬a
imp_iff|Π (Q : Prop), ?P → (?P → Q ↔ Q)
imp_trans|(?a → ?b) → (?b → ?c) → ?a → ?c
imp_true|∀ (a : Prop), a → true ↔ true
implies|Prop → Prop → Prop
imp|Prop → Prop → Prop
imul_comm|∀ (i j : ℤ) (a : ?A), imul i a + imul j a = imul j a + imul i a
imul|ℤ → ?A → ?A
inf.assoc|∀ (a b c : ?A), a ⊓ b ⊓ c = a ⊓ (b ⊓ c)
inf.comm|∀ (a b : ?A), a ⊓ b = b ⊓ a
inf_eq_left|?a ≤ ?b → ?a ⊓ ?b = ?a
inf_le_left|∀ (a b : ?A), a ⊓ b ≤ a
inf_self|∀ (a : ?A), a ⊓ a = a
inf|?A → ?A → ?A
inhabited|Type → Type
int._trans_of_integral_domain_21|semigroup ℤ
int.abstr|ℕ × ℕ → ℤ
int.add_left_inv|∀ (a : ℤ), -a + a = 0
int.add|ℤ → ℤ → ℤ
int.by_cases_of_nat_succ|Π (a : ℤ), (Π (n : ℕ), ?P (int.of_nat n)) → (Π (n : ℕ), ?P (-int.of_nat (nat.succ n))) → ?P a
int.coprime|ℤ → ℤ → Prop
int.div_def|∀ (a b : ℤ), a / b = sign b * int.cases_on a (λ (a : ℕ), int.of_nat (a / int.nat_abs b)) (λ (a : ℕ), int.neg_succ_of_nat (a / int.nat_abs b))
int.div_mul_cancel_of_mod_eq_zero|?a % ?b = 0 → ?a / ?b * ?b = ?a
int.div_neg|∀ (a b : ℤ), a / -b = -(a / b)
int.div_one|∀ (a : ℤ), a / 1 = a
int.div|ℤ → ℤ → ℤ
int.dvd.antisymm|?a ≥ 0 → ?b ≥ 0 → ?a ∣ ?b → ?b ∣ ?a → ?a = ?b
int.dvd_gcd|?a ∣ ?b → ?a ∣ ?c → ?a ∣ int.gcd ?b ?c
int.dvd_lcm_right|∀ (a b : ℤ), b ∣ int.lcm a b
int.dvd_of_mod_eq_zero|?b % ?a = 0 → ?a ∣ ?b
int.eq_zero_of_gcd_eq_zero_left|int.gcd ?a ?b = 0 → ?a = 0
int.eq_zero_of_gcd_eq_zero_right|int.gcd ?a ?b = 0 → ?b = 0
int.eq_zero_or_eq_zero_of_mul_eq_zero|?a * ?b = 0 → ?a = 0 ∨ ?b = 0
int.equiv|ℕ × ℕ → ℕ × ℕ → Prop
int.exists_coprime|int.gcd ?a ?b ≠ 0 → (∃ (a' b' : ℤ), int.gcd a' b' = 1 ∧ ?a = a' * int.gcd ?a ?b ∧ ?b = b' * int.gcd ?a ?b)
int.exists_eq_prod_and_dvd_and_dvd|?c ∣ ?a * ?b → (∃ (a' b' : ℤ), ?c = a' * b' ∧ a' ∣ ?a ∧ b' ∣ ?b)
int.gcd_div|?c ∣ ?a → ?c ∣ ?b → int.gcd (?a / ?c) (?b / ?c) = int.gcd ?a ?b / abs ?c
int.gcd_zero_left|∀ (a : ℤ), int.gcd 0 a = abs a
int.gcd|ℤ → ℤ → ℤ
int.int_has_pow_nat|has_pow_nat ℤ
int.lcm_dvd|?a ∣ ?c → ?b ∣ ?c → int.lcm ?a ?b ∣ ?c
int.lcm_nonneg|∀ (a b : ℤ), int.lcm a b ≥ 0
int.lcm|ℤ → ℤ → ℤ
int.le.elim|?a ≤ ?b → (∃ (n : ℕ), ?a + int.of_nat n = ?b)
int.le_antisymm|?a ≤ ?b → ?b ≤ ?a → ?a = ?b
int.le_refl|∀ (a : ℤ), a ≤ a
int.le|ℤ → ℤ → Prop
int.lt_succ|∀ (a : ℤ), a < a + 1
int.lt|ℤ → ℤ → Prop
int.mod_abs|∀ (a b : ℤ), a % abs b = a % b
int.mod_def|∀ (a b : ℤ), a % b = a - a / b * b
int.mod_lt|∀ (a : ℤ) {b : ℤ}, b ≠ 0 → a % b < abs b
int.mod_one|∀ (a : ℤ), a % 1 = 0
int.mod|ℤ → ℤ → ℤ
int.mul_one|∀ (a : ℤ), a * 1 = a
int.mul_pos|0 < ?a → 0 < ?b → 0 < ?a * ?b
int.mul|ℤ → ℤ → ℤ
int.nat_abs|ℤ → ℕ
int.neg|ℤ → ℤ
int.no_confusion_type|Type → ℤ → ℤ → Type
int.of_nat_dvd_of_nat_iff|∀ (m n : ℕ), int.of_nat m ∣ int.of_nat n ↔ m ∣ n
int.of_nat_nat_abs|∀ (b : ℤ), int.of_nat (int.nat_abs b) = abs b
int.of_nat|ℕ → ℤ
int.of_num|num → ℤ
int.one_mul|∀ (a : ℤ), 1 * a = a
int.pabs|ℕ × ℕ → ℕ
int.padd|ℕ × ℕ → ℕ × ℕ → ℕ × ℕ
int.pmul|ℕ × ℕ → ℕ × ℕ → ℕ × ℕ
int.pneg|ℕ × ℕ → ℕ × ℕ
int.pred|ℤ → ℤ
int.prio|num
int.rec_on|Π (n : ℤ), (Π (a : ℕ), ?C (int.of_nat a)) → (Π (a : ℕ), ?C (int.neg_succ_of_nat a)) → ?C n
int.rec|(Π (a : ℕ), ?C (int.of_nat a)) → (Π (a : ℕ), ?C (int.neg_succ_of_nat a)) → (Π (n : ℤ), ?C n)
int.repr|ℤ → ℕ × ℕ
int.sign_eq_div_abs|∀ (a : ℤ), sign a = a / abs a
int.succ|ℤ → ℤ
int.zero_lt_one|0 < 1
integral_domain._trans_of_to_comm_ring_20|Π (A : Type) [s : integral_domain A], add_group A
integral_domain._trans_of_to_zero_ne_one_class_1|Π (A : Type) [s : integral_domain A], has_zero A
int|Type₁
inv.inj|?a⁻¹ = ?b⁻¹ → ?a = ?b
inv_eq_one_div|∀ (a : ?A), a⁻¹ = 1 / a
inv_eq_one_iff_eq_one|∀ (a : ?A), a⁻¹ = 1 ↔ a = 1
inv_image|(?B → ?B → Prop) → (?A → ?B) → ?A → ?A → Prop
inv_inv|∀ (a : ?A), a⁻¹⁻¹ = a
inv_pow|∀ (a : ?A) (n : ℕ), a⁻¹ ^ n = (a ^ n)⁻¹
inv_zero|0⁻¹ = 0
inv|?A → ?A
is_conj.refl|∀ (a : ?A), is_conjugate a a
is_conj.trans|∀ (a b c : ?A), is_conjugate a b → is_conjugate b c → is_conjugate a c
is_conjugate|?A → ?A → Prop
is_dec_eq|(?A → ?A → bool) → Prop
is_dec_refl|(?A → ?A → bool) → Prop
is_false|Π (c : Prop) [_inst_1 : decidable c], Prop
is_true|Π (c : Prop) [_inst_1 : decidable c], Prop
iterate|(?A → ?A) → ℕ → ?A → ?A
ite|Π (c : Prop) [H : decidable c] {A : Type}, A → A → A
knaster_tarski_dual|nondecreasing ?f → (∃ (a : ?A), ?f a = a ∧ ∀ (b : ?A), ?f b = b → b ≤ a)
knaster_tarski|nondecreasing ?f → (∃ (a : ?A), ?f a = a ∧ ∀ (b : ?A), ?f b = b → a ≤ b)
lattice.mk|Π (le : ?A → ?A → Prop), (∀ (a : ?A), le a a) → (∀ (a b c : ?A), le a b → le b c → le a c) → (∀ (a b : ?A), le a b → le b a → a = b) → (Π (inf sup : ?A → ?A → ?A), (∀ (a b : ?A), le (inf a b) a) → (∀ (a b : ?A), le (inf a b) b) → (∀ (a b c : ?A), le c a → le c b → le c (inf a b)) → (∀ (a b : ?A), le a (sup a b)) → (∀ (a b : ?A), le b (sup a b)) → (∀ (a b c : ?A), le a c → le b c → le (sup a b) c) → lattice ?A)
lattice.no_confusion_type|Type → lattice ?A → lattice ?A → Type
lattice.rec|(Π (le : ?A → ?A → Prop) (le_refl : ∀ (a : ?A), le a a) (le_trans : ∀ (a b c : ?A), le a b → le b c → le a c) (le_antisymm : ∀ (a b : ?A), le a b → le b a → a = b) (inf sup : ?A → ?A → ?A) (inf_le_left : ∀ (a b : ?A), le (inf a b) a) (inf_le_right : ∀ (a b : ?A), le (inf a b) b) (le_inf : ∀ (a b c : ?A), le c a → le c b → le c (inf a b)) (le_sup_left : ∀ (a b : ?A), le a (sup a b)) (le_sup_right : ∀ (a b : ?A), le b (sup a b)) (sup_le : ∀ (a b c : ?A), le a c → le b c → le (sup a b) c), ?C (lattice.mk le le_refl le_trans le_antisymm inf sup inf_le_left inf_le_right le_inf le_sup_left le_sup_right sup_le)) → (Π (n : lattice ?A), ?C n)
lattice.to_weak_order|Π (A : Type) [s : lattice A], weak_order A
lattice_Prop|lattice Prop
lattice_fun|Π (A : Type) (B : Type) [_inst_1 : lattice B], lattice (A → B)
lattice|Type → Type
le.antisymm|?a ≤ ?b → ?b ≤ ?a → ?a = ?b
le.refl|∀ (a : ?A), a ≤ a
le.total|∀ (a b : ?A), a ≤ b ∨ b ≤ a
le.trans|?a ≤ ?b → ?b ≤ ?c → ?a ≤ ?c
le_Inf|(∀ (a : ?A), set.mem a ?s → ?b ≤ a) → ?b ≤ ⨅ ?s
le_Sup|set.mem ?a ?s → ?a ≤ ⨆ ?s
le_abs_self|∀ (a : ?A), a ≤ abs a
le_div_of_mul_le|0 < ?c → ?a * ?c ≤ ?b → ?a ≤ ?b / ?c
le_inf|?c ≤ ?a → ?c ≤ ?b → ?c ≤ ?a ⊓ ?b
le_max_left|∀ (a b : ?A), a ≤ max a b
le_max_right|∀ (a b : ?A), b ≤ max a b
le_min|?c ≤ ?a → ?c ≤ ?b → ?c ≤ min ?a ?b
le_of_eq|?a = ?b → ?a ≤ ?b
le_of_lt|?a < ?b → ?a ≤ ?b
le_of_not_ge|¬?a ≥ ?b → ?a ≤ ?b
le_of_not_gt|¬?a > ?b → ?a ≤ ?b
le_of_one_le_div|?b > 0 → 1 ≤ ?a / ?b → ?b ≤ ?a
le_or_gt|∀ (a b : ?A), a ≤ b ∨ a > b
le_sup_left|∀ (a b : ?A), a ≤ a ⊔ b
le_sup_right|∀ (a b : ?A), b ≤ a ⊔ b
le_top|∀ (a : ?A), a ≤ ⊤
left_distrib|∀ (a b c : ?A), a * (b + c) = a * b + a * c
less_than|ℕ → Type₁
le|?A → ?A → Prop
linear_order_pair.mk|Π (le : ?A → ?A → Prop), (∀ (a : ?A), le a a) → (∀ (a b c : ?A), le a b → le b c → le a c) → (∀ (a b : ?A), le a b → le b a → a = b) → (Π (lt : ?A → ?A → Prop), (∀ (a b : ?A), lt a b → le a b) → (∀ (a b c : ?A), lt a b → le b c → lt a c) → (∀ (a b c : ?A), le a b → lt b c → lt a c) → (∀ (a : ?A), ¬lt a a) → (∀ (a b : ?A), le a b ∨ le b a) → linear_order_pair ?A)
linear_order_pair.no_confusion_type|Type → linear_order_pair ?A → linear_order_pair ?A → Type
linear_order_pair.to_linear_weak_order|Π (A : Type) [s : linear_order_pair A], linear_weak_order A
linear_ordered_comm_ring._trans_of_to_comm_monoid_2|Π (A : Type) [s : linear_ordered_comm_ring A], comm_semigroup A
linear_ordered_comm_ring.mk|Π (add : ?A → ?A → ?A), (∀ (a b c : ?A), add (add a b) c = add a (add b c)) → (Π (zero : ?A), (∀ (a : ?A), add zero a = a) → (∀ (a : ?A), add a zero = a) → (Π (neg : ?A → ?A), (∀ (a : ?A), add (neg a) a = zero) → (∀ (a b : ?A), add a b = add b a) → (Π (mul : ?A → ?A → ?A), (∀ (a b c : ?A), mul (mul a b) c = mul a (mul b c)) → (Π (one : ?A), (∀ (a : ?A), mul one a = a) → (∀ (a : ?A), mul a one = a) → (∀ (a b c : ?A), mul a (add b c) = add (mul a b) (mul a c)) → (∀ (a b c : ?A), mul (add a b) c = add (mul a c) (mul b c)) → (Π (le : ?A → ?A → Prop), (∀ (a : ?A), le a a) → (∀ (a b c : ?A), le a b → le b c → le a c) → (∀ (a b : ?A), le a b → le b a → a = b) → (Π (lt : ?A → ?A → Prop), (∀ (a b : ?A), lt a b → le a b) → (∀ (a b c : ?A), lt a b → le b c → lt a c) → (∀ (a b c : ?A), le a b → lt b c → lt a c) → (∀ (a : ?A), ¬lt a a) → (Π (a b : ?A), le a b → (∀ (c : ?A), le (add c a) (add c b))) → (Π (a b : ?A), lt a b → (∀ (c : ?A), lt (add c a) (add c b))) → zero ≠ one → (∀ (a b : ?A), le zero a → le zero b → le zero (mul a b)) → (∀ (a b : ?A), lt zero a → lt zero b → lt zero (mul a b)) → (∀ (a b : ?A), le a b ↔ lt a b ∨ a = b) → (∀ (a b : ?A), le a b ∨ le b a) → lt zero one → (∀ (a b : ?A), mul a b = mul b a) → linear_ordered_comm_ring ?A))))))
linear_ordered_ring._trans_of_to_linear_ordered_semiring|strong_order_pair ?A
linear_ordered_ring._trans_of_to_ordered_ring_10|Π (A : Type) [s : linear_ordered_ring A], has_lt A
linear_ordered_ring.mk|Π (add : ?A → ?A → ?A), (∀ (a b c : ?A), add (add a b) c = add a (add b c)) → (Π (zero : ?A), (∀ (a : ?A), add zero a = a) → (∀ (a : ?A), add a zero = a) → (Π (neg : ?A → ?A), (∀ (a : ?A), add (neg a) a = zero) → (∀ (a b : ?A), add a b = add b a) → (Π (mul : ?A → ?A → ?A), (∀ (a b c : ?A), mul (mul a b) c = mul a (mul b c)) → (Π (one : ?A), (∀ (a : ?A), mul one a = a) → (∀ (a : ?A), mul a one = a) → (∀ (a b c : ?A), mul a (add b c) = add (mul a b) (mul a c)) → (∀ (a b c : ?A), mul (add a b) c = add (mul a c) (mul b c)) → (Π (le : ?A → ?A → Prop), (∀ (a : ?A), le a a) → (∀ (a b c : ?A), le a b → le b c → le a c) → (∀ (a b : ?A), le a b → le b a → a = b) → (Π (lt : ?A → ?A → Prop), (∀ (a b : ?A), lt a b → le a b) → (∀ (a b c : ?A), lt a b → le b c → lt a c) → (∀ (a b c : ?A), le a b → lt b c → lt a c) → (∀ (a : ?A), ¬lt a a) → (Π (a b : ?A), le a b → (∀ (c : ?A), le (add c a) (add c b))) → (Π (a b : ?A), lt a b → (∀ (c : ?A), lt (add c a) (add c b))) → zero ≠ one → (∀ (a b : ?A), le zero a → le zero b → le zero (mul a b)) → (∀ (a b : ?A), lt zero a → lt zero b → lt zero (mul a b)) → (∀ (a b : ?A), le a b ↔ lt a b ∨ a = b) → (∀ (a b : ?A), le a b ∨ le b a) → lt zero one → linear_ordered_ring ?A))))))
linear_ordered_ring.to_ordered_ring|Π (A : Type) [s : linear_ordered_ring A], ordered_ring A
linear_ordered_semiring.mk|Π (add : ?A → ?A → ?A), (∀ (a b c : ?A), add (add a b) c = add a (add b c)) → (Π (zero : ?A), (∀ (a : ?A), add zero a = a) → (∀ (a : ?A), add a zero = a) → (∀ (a b : ?A), add a b = add b a) → (Π (mul : ?A → ?A → ?A), (∀ (a b c : ?A), mul (mul a b) c = mul a (mul b c)) → (Π (one : ?A), (∀ (a : ?A), mul one a = a) → (∀ (a : ?A), mul a one = a) → (∀ (a b c : ?A), mul a (add b c) = add (mul a b) (mul a c)) → (∀ (a b c : ?A), mul (add a b) c = add (mul a c) (mul b c)) → (∀ (a : ?A), mul zero a = zero) → (∀ (a : ?A), mul a zero = zero) → (∀ (a b c : ?A), add a b = add a c → b = c) → (∀ (a b c : ?A), add a b = add c b → a = c) → (Π (le : ?A → ?A → Prop), (∀ (a : ?A), le a a) → (∀ (a b c : ?A), le a b → le b c → le a c) → (∀ (a b : ?A), le a b → le b a → a = b) → (Π (lt : ?A → ?A → Prop), (∀ (a b : ?A), lt a b → le a b) → (∀ (a b c : ?A), lt a b → le b c → lt a c) → (∀ (a b c : ?A), le a b → lt b c → lt a c) → (∀ (a : ?A), ¬lt a a) → (Π (a b : ?A), le a b → (∀ (c : ?A), le (add c a) (add c b))) → (∀ (a b c : ?A), le (add a b) (add a c) → le b c) → (Π (a b : ?A), lt a b → (∀ (c : ?A), lt (add c a) (add c b))) → (∀ (a b c : ?A), lt (add a b) (add a c) → lt b c) → (∀ (a b c : ?A), le a b → le zero c → le (mul c a) (mul c b)) → (∀ (a b c : ?A), le a b → le zero c → le (mul a c) (mul b c)) → (∀ (a b c : ?A), lt a b → lt zero c → lt (mul c a) (mul c b)) → (∀ (a b c : ?A), lt a b → lt zero c → lt (mul a c) (mul b c)) → (∀ (a b : ?A), le a b ↔ lt a b ∨ a = b) → (∀ (a b : ?A), le a b ∨ le b a) → lt zero one → linear_ordered_semiring ?A)))))
linear_strong_order_pair._trans_of_to_linear_weak_order_1|Π (A : Type) [s : linear_strong_order_pair A], weak_order A
linear_strong_order_pair.mk|Π (le : ?A → ?A → Prop), (∀ (a : ?A), le a a) → (∀ (a b c : ?A), le a b → le b c → le a c) → (∀ (a b : ?A), le a b → le b a → a = b) → (Π (lt : ?A → ?A → Prop), (∀ (a b : ?A), le a b ↔ lt a b ∨ a = b) → (∀ (a : ?A), ¬lt a a) → (∀ (a b : ?A), le a b ∨ le b a) → linear_strong_order_pair ?A)
linear_strong_order_pair.no_confusion_type|Type → linear_strong_order_pair ?A → linear_strong_order_pair ?A → Type
linear_weak_order._trans_of_to_weak_order|Π (A : Type) [s : linear_weak_order A], has_le A
linear_weak_order.cases_on|Π (n : linear_weak_order ?A), (Π (le : ?A → ?A → Prop) (le_refl : ∀ (a : ?A), le a a) (le_trans : ∀ (a b c : ?A), le a b → le b c → le a c) (le_antisymm : ∀ (a b : ?A), le a b → le b a → a = b) (le_total : ∀ (a b : ?A), le a b ∨ le b a), ?C (linear_weak_order.mk le le_refl le_trans le_antisymm le_total)) → ?C n
linear_weak_order.induction_on|Π (n : linear_weak_order ?A), (Π (le : ?A → ?A → Prop) (le_refl : ∀ (a : ?A), le a a) (le_trans : ∀ (a b c : ?A), le a b → le b c → le a c) (le_antisymm : ∀ (a b : ?A), le a b → le b a → a = b) (le_total : ∀ (a b : ?A), le a b ∨ le b a), ?C (linear_weak_order.mk le le_refl le_trans le_antisymm le_total)) → ?C n
linear_weak_order.mk|Π (le : ?A → ?A → Prop), (∀ (a : ?A), le a a) → (∀ (a b c : ?A), le a b → le b c → le a c) → (∀ (a b : ?A), le a b → le b a → a = b) → (∀ (a b : ?A), le a b ∨ le b a) → linear_weak_order ?A
linear_weak_order.no_confusion_type|Type → linear_weak_order ?A → linear_weak_order ?A → Type
linear_weak_order.no_confusion|?v1 = ?v2 → linear_weak_order.no_confusion_type ?P ?v1 ?v2
linear_weak_order.rec_on|Π (n : linear_weak_order ?A), (Π (le : ?A → ?A → Prop) (le_refl : ∀ (a : ?A), le a a) (le_trans : ∀ (a b c : ?A), le a b → le b c → le a c) (le_antisymm : ∀ (a b : ?A), le a b → le b a → a = b) (le_total : ∀ (a b : ?A), le a b ∨ le b a), ?C (linear_weak_order.mk le le_refl le_trans le_antisymm le_total)) → ?C n
linear_weak_order.to_weak_order|Π (A : Type) [s : linear_weak_order A], weak_order A
list.all_inter_of_all_right|∀ (l₁ : list ?A) {l₂ : list ?A}, list.all l₂ ?p → list.all (list.inter l₁ l₂) ?p
list.all_nil|∀ (p : ?A → Prop), list.all list.nil p
list.all|list ?A → (?A → Prop) → Prop
list.any_cons|∀ (p : ?A → Prop) (a : ?A) (l : list ?A), list.any (list.cons a l) p = (p a ∨ list.any l p)
list.any_nil|∀ (p : ?A → Prop), list.any list.nil p = false
list.any|list ?A → (?A → Prop) → Prop
list.append_nil_right|∀ (t : list ?T), list.append t list.nil = t
list.append|list ?T → list ?T → list ?T
list.as_type.no_confusion_type|Type → list.as_type ?l → list.as_type ?l → Type
list.as_type.rec|(Π (value : ?A) (is_member : list.mem value ?l), ?C (list.as_type.mk value is_member)) → (Π (n : list.as_type ?l), ?C n)
list.as_type|list ?A → Type
list.below|list ?T → Type
list.brec_on|Π (n : list ?T), (Π (n : list ?T), list.below n → ?C n) → ?C n
list.concat|?T → list ?T → list ?T
list.cons|?T → list ?T → list ?T
list.count_cons_eq|∀ (a : ?A) (l : list ?A), list.count a (list.cons a l) = nat.succ (list.count a l)
list.count_eq_zero_of_not_mem|¬list.mem ?a ?l → list.count ?a ?l = 0
list.count|?A → list ?A → ℕ
list.dinj|Π (p : ?A → Prop), (Π (a : ?A), p a → ?B) → Prop
list.dinj₁|Π (p : ?A → Prop), (Π (a : ?A), p a → ?B) → Prop
list.disjoint.comm|list.disjoint ?l₁ ?l₂ → list.disjoint ?l₂ ?l₁
list.disjoint_cons_of_not_mem_of_disjoint|¬list.mem ?a ?l₂ → list.disjoint ?l₁ ?l₂ → list.disjoint (list.cons ?a ?l₁) ?l₂
list.disjoint_left|list.disjoint ?l₁ ?l₂ → (∀ {a : ?A}, list.mem a ?l₁ → ¬list.mem a ?l₂)
list.disjoint_nil_left|∀ (l : list ?A), list.disjoint list.nil l
list.disjoint_nil_right|∀ (l : list ?A), list.disjoint l list.nil
list.disjoint_of_disjoint_append_right_left|list.disjoint ?l (list.append ?l₁ ?l₂) → list.disjoint ?l ?l₁
list.disjoint_of_disjoint_cons_left|list.disjoint (list.cons ?a ?l₁) ?l₂ → list.disjoint ?l₁ ?l₂
list.disjoint_of_nodup_append|list.nodup (list.append ?l₁ ?l₂) → list.disjoint ?l₁ ?l₂
list.dmap|Π (p : ?A → Prop) [h : decidable_pred p], (Π (a : ?A), p a → ?B) → list ?A → list ?B
list.dropn|ℕ → list ?A → list ?A
list.eq_nil_of_length_eq_zero|list.length ?l = 0 → ?l = list.nil
list.erase|?A → list ?A → list ?A
list.filter|Π (p : ?A → Prop) [h : decidable_pred p], list ?A → list ?A
list.find_nil|∀ (x : ?T), list.find x list.nil = 0
list.find|?T → list ?T → ℕ
list.firstn|ℕ → list ?A → list ?A
list.flat|list (list ?A) → list ?A
list.foldl_union_of_disjoint|∀ (f : ?B → ?A → ?B) (b : ?B) {l₁ l₂ : list ?A}, list.disjoint l₁ l₂ → list.foldl f b (list.union l₁ l₂) = list.foldl f (list.foldl f b l₁) l₂
list.foldl|(?A → ?B → ?A) → ?A → list ?B → ?A
list.foldr_union_of_dijoint|∀ (f : ?A → ?B → ?B) (b : ?B) {l₁ l₂ : list ?A}, list.disjoint l₁ l₂ → list.foldr f b (list.union l₁ l₂) = list.foldr f (list.foldr f b l₂) l₁
list.foldr|(?A → ?B → ?B) → ?B → list ?A → ?B
list.head|list ?T → ?T
list.ibelow|list ?T → Prop
list.insert|?A → list ?A → list ?A
list.inter_eq_nil_of_disjoint|list.disjoint ?l₁ ?l₂ → list.inter ?l₁ ?l₂ = list.nil
list.inter|list ?A → list ?A → list ?A
list.inth|list ?T → ℕ → ?T
list.ith_succ|∀ (a : ?T) (l : list ?T) (i : ℕ) (h : nat.succ i < list.length (list.cons a l)), list.ith (list.cons a l) (nat.succ i) h = list.ith l i (nat.lt_of_succ_lt_succ h)
list.ith|Π (l : list ?T) (i : ℕ), i < list.length l → ?T
list.last|Π (l : list ?T), l ≠ list.nil → ?T
list.length_eq_of_qeq|list.qeq ?a ?l₂ ?l₁ → list.length ?l₁ = nat.succ (list.length ?l₂)
list.length_reverse|∀ (l : list ?T), list.length (list.reverse l) = list.length l
list.length|list ?T → ℕ
list.map_cons|∀ (f : ?A → ?B) (a : ?A) (l : list ?A), list.map f (list.cons a l) = list.cons (f a) (list.map f l)
list.map_id'|(∀ (x : ?A), ?f x = x) → (∀ (l : list ?A), list.map ?f l = l)
list.map_id|∀ (l : list ?A), list.map id l = l
list.map_map|∀ (g : ?B → ?C) (f : ?A → ?B) (l : list ?A), list.map g (list.map f l) = list.map (function.comp g f) l
list.map_nil|∀ (f : ?A → ?B), list.map f list.nil = list.nil
list.map_reverse|∀ (f : ?A → ?B) (l : list ?A), list.map f (list.reverse l) = list.reverse (list.map f l)
list.map|(?A → ?B) → list ?A → list ?B
list.map₂|(?A → ?B → ?C) → list ?A → list ?B → list ?C
list.mem_dmap|∀ (Pa : ?p ?a), list.mem ?a ?l → list.mem (?f ?a Pa) (list.dmap ?p ?f ?l)
list.mem_map|∀ (f : ?A → ?B) {a : ?A} {l : list ?A}, list.mem a l → list.mem (f a) (list.map f l)
list.mem_union_right|∀ (l₁ : list ?A) {l₂ : list ?A}, list.mem ?a l₂ → list.mem ?a (list.union l₁ l₂)
list.mem|?T → list ?T → Prop
list.nil_sub|∀ (l : list ?T), list.sublist list.nil l
list.nil|list ?T
list.nodup_union_of_nodup_of_nodup|list.nodup ?l₁ → list.nodup ?l₂ → list.nodup (list.union ?l₁ ?l₂)
list.nodup|list ?A → Prop
list.not_mem_dmap_of_dinj_of_not_mem|list.dinj ?p ?f → (∀ {l : list ?A} {a : ?A} (Pa : ?p a), ¬list.mem a l → ¬list.mem (?f a Pa) (list.dmap ?p ?f l))
list.not_mem_of_find_eq_length|list.find ?a ?l = list.length ?l → ¬list.mem ?a ?l
list.nth_succ|∀ (a : ?T) (l : list ?T) (n : ℕ), list.nth (list.cons a l) (nat.succ n) = list.nth l n
list.nth|list ?T → ℕ → option ?T
list.product|list ?A → list ?B → list (?A × ?B)
list.qeq.rec|(Π (l : list ?A), ?C l (list.cons ?a l)) → (Π (b : ?A) {l l' : list ?A}, list.qeq ?a l l' → ?C l l' → ?C (list.cons b l) (list.cons b l')) → (Π {a a_1 : list ?A}, list.qeq ?a a a_1 → ?C a a_1)
list.qeq_app|∀ (l₁ : list ?A) (a : ?A) (l₂ : list ?A), list.qeq a (list.append l₁ l₂) (list.append l₁ (list.cons a l₂))
list.qeq|?A → list ?A → list ?A → Prop
list.rec_on|Π (n : list ?T), ?C list.nil → (Π (a : ?T) (a_1 : list ?T), ?C a_1 → ?C (list.cons a a_1)) → ?C n
list.rec|?C list.nil → (Π (a : ?T) (a_1 : list ?T), ?C a_1 → ?C (list.cons a a_1)) → (Π (n : list ?T), ?C n)
list.reverse|list ?T → list ?T
list.sub_cons|∀ (a : ?T) (l : list ?T), list.sublist l (list.cons a l)
list.sublist|list ?T → list ?T → Prop
list.tail|list ?T → list ?T
list.union|list ?A → list ?A → list ?A
list.unzip_cons|∀ (a : ?A) (b : ?B) (l : list (?A × ?B)), list.unzip (list.cons (a, b) l) = prod.cases_on (list.unzip l) (λ (a_1 : list ?A) (a_1_1 : list ?B), (list.cons a a_1, list.cons b a_1_1))
list.unzip|list (?A × ?B) → list ?A × list ?B
list.upto|ℕ → list ℕ
list.zip_unzip|∀ (l : list (?A × ?B)), list.zip (prod.pr1 (list.unzip l)) (prod.pr2 (list.unzip l)) = l
list.zip|list ?A → list ?B → list (?A × ?B)
list|Type → Type
lt.asymm|?a < ?b → ¬?b < ?a
lt.by_cases|(?a < ?b → ?P) → (?a = ?b → ?P) → (?b < ?a → ?P) → ?P
lt.cases|?A → ?A → ?B → ?B → ?B → ?B
lt.irrefl|∀ (a : ?A), ¬a < a
lt.trans|?a < ?b → ?b < ?c → ?a < ?c
lt.trichotomy|∀ (a b : ?A), a < b ∨ a = b ∨ b < a
lt_add_of_neg_add_lt_left|-?b + ?a < ?c → ?a < ?b + ?c
lt_div_of_mul_lt|0 < ?c → ?a * ?c < ?b → ?a < ?b / ?c
lt_min|?a < ?b → ?a < ?c → ?a < min ?b ?c
lt_of_not_ge|¬?a ≥ ?b → ?a < ?b
lt_of_one_div_lt_one_div_of_neg|?b < 0 → 1 / ?a < 1 / ?b → ?b < ?a
lt_of_one_div_lt_one_div|0 < ?a → 1 / ?a < 1 / ?b → ?b < ?a
lt_or_ge|∀ (a b : ?A), a < b ∨ a ≥ b
lt|?A → ?A → Prop
map.inverse|set.map ?a ?b → (Π {dflt : ?X}, set.mem dflt ?a → set.map ?b ?a)
max.assoc|∀ (a b c : ?A), max (max a b) c = max a (max b c)
max.comm|∀ (a b : ?A), max a b = max b a
max.left_comm|∀ (a b c : ?A), max a (max b c) = max b (max a c)
max.right_comm|∀ (a b c : ?A), max (max a b) c = max (max a c) b
max_add_add_left|max (?a + ?b) (?a + ?c) = ?a + max ?b ?c
max_add_add_right|max (?a + ?c) (?b + ?c) = max ?a ?b + ?c
max_eq_left_of_lt|?b < ?a → max ?a ?b = ?a
max_eq_left|?b ≤ ?a → max ?a ?b = ?a
max_eq_neg_min_neg_neg|max ?a ?b = -min (-?a) (-?b)
max_eq_right_of_lt|?a < ?b → max ?a ?b = ?b
max_eq_right|?a ≤ ?b → max ?a ?b = ?b
max_le|?a ≤ ?c → ?b ≤ ?c → max ?a ?b ≤ ?c
max_lt|?a < ?c → ?b < ?c → max ?a ?b < ?c
max_neg_neg|max (-?a) (-?b) = -min ?a ?b
max_self|∀ (a : ?A), max a a = a
max|?A → ?A → ?A
measurable.cases_on|Π (n : measurable ?A), (Π (a : ?A → ℕ), ?C (measurable.mk a)) → ?C n
measurable.mk|(?A → ℕ) → measurable ?A
measurable.rec_on|Π (n : measurable ?A), (Π (a : ?A → ℕ), ?C (measurable.mk a)) → ?C n
measurable.rec|(Π (a : ?A → ℕ), ?C (measurable.mk a)) → (Π (n : measurable ?A), ?C n)
measurable|Type → Type
min.assoc|∀ (a b c : ?A), min (min a b) c = min a (min b c)
min.comm|∀ (a b : ?A), min a b = min b a
min.left_comm|∀ (a b c : ?A), min a (min b c) = min b (min a c)
min.right_comm|∀ (a b c : ?A), min (min a b) c = min (min a c) b
min_add_add_left|min (?a + ?b) (?a + ?c) = ?a + min ?b ?c
min_add_add_right|min (?a + ?c) (?b + ?c) = min ?a ?b + ?c
min_eq_left_of_lt|?a < ?b → min ?a ?b = ?a
min_eq_left|?a ≤ ?b → min ?a ?b = ?a
min_eq_neg_max_neg_neg|min ?a ?b = -max (-?a) (-?b)
min_eq_right_of_lt|?b < ?a → min ?a ?b = ?b
min_eq_right|?b ≤ ?a → min ?a ?b = ?b
min_le_left|∀ (a b : ?A), min a b ≤ a
min_le_right|∀ (a b : ?A), min a b ≤ b
min_neg_neg|min (-?a) (-?b) = -max ?a ?b
min_self|∀ (a : ?A), min a a = a
min|?A → ?A → ?A
mk_equivalence|∀ (R : ?B → ?B → Prop), reflexive R → symmetric R → transitive R → equivalence R
mod|?A → ?A → ?A
monoid.cases_on|Π (n : monoid ?A), (Π (mul : ?A → ?A → ?A) (mul_assoc : ∀ (a b c : ?A), mul (mul a b) c = mul a (mul b c)) (one : ?A) (one_mul : ∀ (a : ?A), mul one a = a) (mul_one : ∀ (a : ?A), mul a one = a), ?C (monoid.mk mul mul_assoc one one_mul mul_one)) → ?C n
monoid.destruct|Π (n : monoid ?A), (Π (mul : ?A → ?A → ?A) (mul_assoc : ∀ (a b c : ?A), mul (mul a b) c = mul a (mul b c)) (one : ?A) (one_mul : ∀ (a : ?A), mul one a = a) (mul_one : ∀ (a : ?A), mul a one = a), ?C (monoid.mk mul mul_assoc one one_mul mul_one)) → ?C n
monoid.induction_on|Π (n : monoid ?A), (Π (mul : ?A → ?A → ?A) (mul_assoc : ∀ (a b c : ?A), mul (mul a b) c = mul a (mul b c)) (one : ?A) (one_mul : ∀ (a : ?A), mul one a = a) (mul_one : ∀ (a : ?A), mul a one = a), ?C (monoid.mk mul mul_assoc one one_mul mul_one)) → ?C n
monoid.mk|Π (mul : ?A → ?A → ?A), (∀ (a b c : ?A), mul (mul a b) c = mul a (mul b c)) → (Π (one : ?A), (∀ (a : ?A), mul one a = a) → (∀ (a : ?A), mul a one = a) → monoid ?A)
monoid.no_confusion|?v1 = ?v2 → monoid.no_confusion_type ?P ?v1 ?v2
monoid.pow|?A → ℕ → ?A
monoid.rec_on|Π (n : monoid ?A), (Π (mul : ?A → ?A → ?A) (mul_assoc : ∀ (a b c : ?A), mul (mul a b) c = mul a (mul b c)) (one : ?A) (one_mul : ∀ (a : ?A), mul one a = a) (mul_one : ∀ (a : ?A), mul a one = a), ?C (monoid.mk mul mul_assoc one one_mul mul_one)) → ?C n
monoid.rec|(Π (mul : ?A → ?A → ?A) (mul_assoc : ∀ (a b c : ?A), mul (mul a b) c = mul a (mul b c)) (one : ?A) (one_mul : ∀ (a : ?A), mul one a = a) (mul_one : ∀ (a : ?A), mul a one = a), ?C (monoid.mk mul mul_assoc one one_mul mul_one)) → (Π (n : monoid ?A), ?C n)
monoid.to_has_one|Π (A : Type) [s : monoid A], has_one A
monoid.to_semigroup|Π (A : Type) [s : monoid A], semigroup A
monoid_has_pow_nat|has_pow_nat ?A
monoid|Type → Type
mt|(?a → ?b) → ¬?b → ¬?a
mul.assoc|∀ (a b c : ?A), (:a * b * c:) = (:a * (b * c):)
mul.comm|∀ (a b : ?A), a * b = b * a
mul.left_cancel|?a * ?b = ?a * ?c → ?b = ?c
mul.left_comm|∀ (a b c : ?A), a * (b * c) = b * (a * c)
mul.left_inv|∀ (a : ?A), a⁻¹ * a = 1
mul.right_cancel|?a * ?b = ?c * ?b → ?a = ?c
mul.right_comm|∀ (a b c : ?A), a * b * c = a * c * b
mul.right_inv|∀ (a : ?A), a * a⁻¹ = 1
mul_div_assoc|∀ (a b : ?A), a * b / ?c = a * (b / ?c)
mul_div_cancel'|?b ≠ 0 → ?b * (?a / ?b) = ?a
mul_div_cancel_left|?a ≠ 0 → ?a * ?b / ?a = ?b
mul_div_cancel|∀ (a : ?A) {b : ?A}, b ≠ 0 → a * b / b = a
mul_div_mul_left'|∀ (a b : ?A) {c : ?A}, c ≠ 0 → c * a / (c * b) = a / b
mul_div_mul_left|∀ (a : ?A) {b c : ?A}, b ≠ 0 → c ≠ 0 → c * a / (c * b) = a / b
mul_div_mul_right'|∀ (a b : ?A) {c : ?A}, c ≠ 0 → a * c / (b * c) = a / b
mul_div_mul_right|∀ (a : ?A) {b c : ?A}, b ≠ 0 → c ≠ 0 → a * c / (b * c) = a / b
mul_dvd_mul|?a ∣ ?b → ?c ∣ ?d → ?a * ?c ∣ ?b * ?d
mul_eq_of_eq_div|∀ (a b : ?A) {c : ?A}, c ≠ 0 → a = b / c → a * c = b
mul_inv'|∀ (a b : ?A), (b * a)⁻¹ = a⁻¹ * b⁻¹
mul_inv_cancel_left|∀ (a b : ?A), a * (a⁻¹ * b) = b
mul_inv_cancel|?a ≠ 0 → ?a * ?a⁻¹ = 1
mul_inv_eq|?a ≠ 0 → ?b ≠ 0 → (?b * ?a)⁻¹ = ?a⁻¹ * ?b⁻¹
mul_inv|∀ (a b : ?A), (a * b)⁻¹ = b⁻¹ * a⁻¹
mul_le_mul|?a ≤ ?c → ?b ≤ ?d → 0 ≤ ?b → 0 ≤ ?c → ?a * ?b ≤ ?c * ?d
mul_le_of_le_div|0 < ?c → ?a ≤ ?b / ?c → ?a * ?c ≤ ?b
mul_left_cancel|?a * ?b = ?a * ?c → ?b = ?c
mul_lt_mul'|?a < ?c → ?b < ?d → ?b ≥ 0 → ?c > 0 → ?a * ?b < ?c * ?d
mul_lt_mul|?a < ?c → ?b ≤ ?d → 0 < ?b → 0 ≤ ?c → ?a * ?b < ?c * ?d
mul_lt_of_lt_div|0 < ?c → ?a < ?b / ?c → ?a * ?c < ?b
mul_mul_div|∀ (a : ?A) {c : ?A}, c ≠ 0 → a = a * c * (1 / c)
mul_ne_zero_comm|?a * ?b ≠ 0 → ?b * ?a ≠ 0
mul_ne_zero|?a ≠ 0 → ?b ≠ 0 → ?a * ?b ≠ 0
mul_neg_one_eq_neg|∀ (a : ?A), a * -1 = -a
mul_nmul|∀ (m n : ℕ) (a : ?A), (m * n)⬝a = m⬝(n⬝a)
mul_nonneg|?a ≥ 0 → ?b ≥ 0 → ?a * ?b ≥ 0
mul_one_div_cancel|?a ≠ 0 → ?a * (1 / ?a) = 1
mul_one|∀ (a : ?A), a * 1 = a
mul_pos|?a > 0 → ?b > 0 → ?a * ?b > 0
mul_pow|∀ (a b : ?A) (n : ℕ), (a * b) ^ n = a ^ n * b ^ n
mul_right_cancel|?a * ?b = ?c * ?b → ?a = ?c
mul_self_eq_one_iff|∀ (a : ?A), a * a = 1 ↔ a = 1 ∨ a = -1
mul_self_nonneg|∀ (a : ?A), a * a ≥ 0
mul_self_sub_one_eq|∀ (a : ?A), a * a - 1 = (a + 1) * (a - 1)
mul_zero_class.mk|Π (mul : ?A → ?A → ?A) (zero : ?A), (∀ (a : ?A), mul zero a = zero) → (∀ (a : ?A), mul a zero = zero) → mul_zero_class ?A
mul_zero_class.rec|(Π (mul : ?A → ?A → ?A) (zero : ?A) (zero_mul : ∀ (a : ?A), mul zero a = zero) (mul_zero : ∀ (a : ?A), mul a zero = zero), ?C (mul_zero_class.mk mul zero zero_mul mul_zero)) → (Π (n : mul_zero_class ?A), ?C n)
mul_zero_class|Type → Type
mul_zero|∀ (a : ?A), a * 0 = 0
mulf|(?A → ?B) → ?B → ?A → ?B
mul|?A → ?A → ?A
nat._trans_of_comm_semiring_2|comm_semigroup ℕ
nat.add_one_ne_zero|∀ (n : ℕ), n + 1 ≠ 0
nat.add_zero|∀ (n : ℕ), n + 0 = n
nat.addl|ℕ → ℕ → ℕ
nat.add|ℕ → ℕ → ℕ
nat.ball_zero|∀ (P : ℕ → Prop), nat.ball 0 P
nat.ball|ℕ → (ℕ → Prop) → Prop
nat.below|ℕ → Type
nat.bex_of_bsub|nat.bsub ?n ?P → nat.bex ?n ?P
nat.bex_succ_of_pred|?P ?a → nat.bex (nat.succ ?a) ?P
nat.bex|ℕ → (ℕ → Prop) → Prop
nat.bsub|ℕ → (ℕ → Prop) → Type₁
nat.by_cases_zero_pos|Π (y : ℕ), ?P 0 → (Π {y : ℕ}, y > 0 → ?P y) → ?P y
nat.coprime_of_coprime_mul_right_right|nat.coprime ?m (?n * ?k) → nat.coprime ?m ?n
nat.coprime|ℕ → ℕ → Prop
nat.decidable_even|Π (n : ℕ), decidable (nat.even n)
nat.dist.triangle_inequality|∀ (n m k : ℕ), nat.dist n k ≤ nat.dist n m + nat.dist m k
nat.dist|ℕ → ℕ → ℕ
nat.div_eq_zero_of_lt|?a < ?b → ?a / ?b = 0
nat.div_one|∀ (n : ℕ), n / 1 = n
nat.div|ℕ → ℕ → ℕ
nat.dvd.antisymm|?m ∣ ?n → ?n ∣ ?m → ?m = ?n
nat.dvd_gcd|?k ∣ ?m → ?k ∣ ?n → ?k ∣ nat.gcd ?m ?n
nat.dvd_lcm_right|∀ (m n : ℕ), n ∣ nat.lcm m n
nat.dvd_pow_of_dvd_of_pos|?i ∣ ?j → ?n > 0 → ?i ∣ ?j ^ ?n
nat.eq_one_of_mul_eq_one_right|?n * ?m = 1 → ?n = 1
nat.eq_one_of_mul_eq_self_left|?n > 0 → ?m * ?n = ?n → ?m = 1
nat.eq_zero_or_pos|∀ (n : ℕ), n = 0 ∨ n > 0
nat.even_zero|nat.even 0
nat.even|ℕ → Prop
nat.fact_le|?m ≤ ?n → nat.fact ?m ≤ nat.fact ?n
nat.fact|ℕ → ℕ
nat.find|Exists ?p → ℕ
nat.gcd.F|Π (p₁ : ℕ × ℕ), (Π (p₂ : ℕ × ℕ), pair_nat.lt p₂ p₁ → ℕ) → ℕ
nat.gcd_dvd_left|∀ (m n : ℕ), nat.gcd m n ∣ m
nat.gcd_eq_one_of_coprime|nat.coprime ?m ?n → nat.gcd ?m ?n = 1
nat.gcd|ℕ → ℕ → ℕ
nat.ibelow|ℕ → Prop
nat.lcm_dvd|?m ∣ ?k → ?n ∣ ?k → nat.lcm ?m ?n ∣ ?k
nat.lcm|ℕ → ℕ → ℕ
nat.le.rec|?C ?a → (Π {b : ℕ}, nat.le ?a b → ?C b → ?C (nat.succ b)) → (Π {a : ℕ}, nat.le ?a a → ?C a)
nat.le.step|nat.le ?a ?b → nat.le ?a (nat.succ ?b)
nat.le_refl|∀ (a : ℕ), a ≤ a
nat.le_three_of_sqrt_eq_one|nat.sqrt ?n = 1 → ?n ≤ 3
nat.least|Π (P : ℕ → Prop) [decP : Π (n : ℕ), decidable (P n)], ℕ → ℕ
nat.le|ℕ → ℕ → Prop
nat.lt.base|∀ (n : ℕ), n < nat.succ n
nat.lt.wf|well_founded lt
nat.lt_ge_by_cases|(?a < ?b → ?P) → (?a ≥ ?b → ?P) → ?P
nat.lt_le_antisymm|?n < ?m → ?m ≤ ?n → false
nat.lt|ℕ → ℕ → Prop
nat.measure.wf|∀ (f : ?A → ℕ), well_founded (nat.measure f)
nat.mkpair_unpair|∀ (n : ℕ), nat.mkpair (prod.pr1 (nat.unpair n)) (prod.pr2 (nat.unpair n)) = n
nat.mkpair|ℕ → ℕ → ℕ
nat.mod_le|?x % ?y ≤ ?x
nat.mod_lt|∀ (x : ℕ) {y : ℕ}, y > 0 → x % y < y
nat.mod_one|∀ (n : ℕ), n % 1 = 0
nat.mod_zero|∀ (a : ℕ), a % 0 = a
nat.mod|ℕ → ℕ → ℕ
nat.mul_div_cancel_of_mod_eq_zero|?m % ?n = 0 → ?n * (?m / ?n) = ?m
nat.mul_le_mul|?n ≤ ?k → ?m ≤ ?l → ?n * ?m ≤ ?k * ?l
nat.mul|ℕ → ℕ → ℕ
nat.nat_has_mul|has_mul ℕ
nat.ne_zero_of_pos|?n > 0 → ?n ≠ 0
nat.not_ball_succ_of_not_ball|¬nat.ball ?n ?P → ¬nat.ball (nat.succ ?n) ?P
nat.not_lt_zero|∀ (a : ℕ), ¬a < 0
nat.not_odd_zero|¬nat.odd 0
nat.not_succ_le_self|¬nat.succ ?n ≤ ?n
nat.odd_iff_not_even|∀ (n : ℕ), nat.odd n ↔ ¬nat.even n
nat.odd_of_odd_pow|?m > 0 → nat.odd (?n ^ ?m) → nat.odd ?n
nat.odd_succ_of_even|nat.even ?n → nat.odd (nat.succ ?n)
nat.odd|ℕ → Prop
nat.of_num|num → ℕ
nat.one_mul|∀ (n : ℕ), 1 * n = n
nat.pow_div_cancel|?a ≠ 0 → ?a ^ nat.succ ?b / ?a = ?a ^ ?b
nat.pow_dvd_of_pow_succ_dvd|?p ^ nat.succ ?i ∣ ?n → ?p ^ ?i ∣ ?n
nat.pred_succ|∀ (n : ℕ), nat.pred (nat.succ n) = n
nat.pred_zero|nat.pred 0 = 0
nat.pred|ℕ → ℕ
nat.prio|num
nat.rec_on|Π (n : ℕ), ?C 0 → (Π (a : ℕ), ?C a → ?C (nat.succ a)) → ?C n
nat.rec|?C 0 → (Π (a : ℕ), ?C a → ?C (nat.succ a)) → (Π (n : ℕ), ?C n)
nat.sqrt_aux_lower|?s ≤ ?n → nat.sqrt_aux ?s ?n * nat.sqrt_aux ?s ?n ≤ ?n
nat.sqrt_le|∀ (n : ℕ), nat.sqrt n ≤ n
nat.sqrt|ℕ → ℕ
nat.sub_eq_of_add_eq|?n + ?m = ?k → ?k - ?n = ?m
nat.sub_eq_zero_of_le|?n ≤ ?m → ?n - ?m = 0
nat.sub_le|∀ (a b : ℕ), a - b ≤ a
nat.sub_lt|0 < ?a → 0 < ?b → ?a - ?b < ?a
nat.sub_sub|∀ (n m k : ℕ), (:n - m - k:) = (:n - (m + k):)
nat.sub|ℕ → ℕ → ℕ
nat.succ_add_eq_succ_add|∀ (n m : ℕ), nat.succ n + m = n + nat.succ m
nat.succ|ℕ → ℕ
nat.unpair_lt_aux|?n ≥ 1 → prod.pr1 (nat.unpair ?n) < ?n
nat.unpair|ℕ → ℕ × ℕ
nat.zero_div|∀ (b : ℕ), 0 / b = 0
nat.zero_le_one|0 ≤ 1
nat.zero_sub_eq_zero|∀ (a : ℕ), 0 - a = 0
nat.zero_sub|∀ (n : ℕ), 0 - n = 0
nat.zero|ℕ
nat_has_add|has_add ℕ
nat|Type₁
ne.def|∀ (a b : ?A), a ≠ b = ¬a = b
ne.elim|?a ≠ ?b → ?a = ?b → false
ne.intro|(?a = ?b → false) → ?a ≠ ?b
ne.irrefl|?a ≠ ?a → false
ne.symm|?a ≠ ?b → ?b ≠ ?a
ne_add_of_ne_zero_left|∀ (a : ?A) {b : ?A}, b ≠ 0 → a ≠ a + b
ne_add_of_ne_zero_right|∀ (a : ?A) {b : ?A}, b ≠ 0 → a ≠ b + a
ne_of_gt|?a > ?b → ?a ≠ ?b
ne_of_lt|?a < ?b → ?a ≠ ?b
neg.inj|-?a = -?b → ?a = ?b
neg_add_rev|∀ (a b : ?A), -(a + b) = -b + -a
neg_add|∀ (a b : ?A), -(a + b) = -a + -b
neg_div|∀ (a b : ?A), -b / a = -(b / a)
neg_dvd_iff_dvd|∀ (a b : ?A), -a ∣ b ↔ a ∣ b
neg_eq_neg_iff_eq|∀ (a b : ?A), -a = -b ↔ a = b
neg_le_neg|?a ≤ ?b → -?b ≤ -?a
neg_lt_neg|?a < ?b → -?b < -?a
neg_mul_eq_mul_neg|∀ (a b : ?A), -(a * b) = a * -b
neg_mul_eq_neg_mul_symm|∀ (a b : ?A), -a * b = -(a * b)
neg_neg|∀ (a : ?A), - -a = a
neg_sub|∀ (a b : ?A), -(a - b) = b - a
neg_zero|-0 = 0
neg|?A → ?A
ne|?A → ?A → Prop
nmul_add|∀ (n : ℕ) (a b : ?A), n⬝(a + b) = n⬝a + n⬝b
nmul_comm|∀ (m n : ℕ) (a : ?A), m⬝a + n⬝a = n⬝a + m⬝a
nmul_neg|∀ (n : ℕ) (a : ?A), n⬝-a = -(n⬝a)
nmul_zero|∀ (n : ℕ), n⬝0 = 0
nmul|ℕ → ?A → ?A
no_zero_divisors.no_confusion_type|Type → no_zero_divisors ?A → no_zero_divisors ?A → Type
nodup_list|Type → Type
non_contradictory_em|∀ (a : Prop), ¬¬(a ∨ ¬a)
nondecreasing_of_neg_nonincreasing|nonincreasing (λ (x : ?B), -?f x) → nondecreasing ?f
nonempty.rec_on|nonempty ?A → (?A → ?C) → ?C
nonempty|Type → Prop
norm_num.bit0_add_bit1|∀ (a b : ?A), bit0 a + bit1 b = bit1 (a + b)
norm_num.mk_cong|∀ (op : ?A → ?A) (a b : ?A), a = b → op a = op b
norm_num.nonzero_of_div_helper|∀ (a b : ?A), a ≠ 0 → b ≠ 0 → a / b ≠ 0
norm_num.zero_mul|∀ (a : ?A), 0 * a = 0
not.elim|¬?a → ?a → ?A
not.intro|(?a → false) → ¬?a
not.mto|(?a → ?b) → ¬?b → ¬?a
not_congr|(?a ↔ ?b) → (¬?a ↔ ¬?b)
not_false|¬false
not_lt_self|∀ (a : ?A), ¬a < a
not_not_em|¬¬(?a ∨ ¬?a)
not_not_iff|∀ (a : Prop) [D : decidable a], ¬¬a ↔ a
not_or|¬?a → ¬?b → ¬(?a ∨ ?b)
not_true|¬true ↔ false
not|Prop → Prop
num.add|num → num → num
num.le|num → num → bool
num.mul|num → num → num
num.pos|pos_num → num
num.pred|num → num
num.rec_on|Π (n : num), ?C 0 → (Π (a : pos_num), ?C (num.pos a)) → ?C n
num.rec|?C 0 → (Π (a : pos_num), ?C (num.pos a)) → (Π (n : num), ?C n)
num.size|num → num
num.sub|num → num → num
num.succ|num → num
num.zero|num
num_has_add|has_add num
num|Type₁
of_eq_true|?p = true → ?p
of_heq_true|?a == true → ?a
of_iff_true|(?a ↔ true) → ?a
of_is_true|is_true ?c → ?c
of_not_is_false|¬is_false ?c → ?c
one_add_one_eq_two|1 + 1 = 2
one_add_one_ne_zero|1 + 1 ≠ 0
one_div_add_one_div|?a ≠ 0 → ?b ≠ 0 → 1 / ?a + 1 / ?b = (?a + ?b) / (?a * ?b)
one_div_div|∀ (a b : ?A), 1 / (a / b) = b / a
one_div_le_neg_one|?a < 0 → -1 ≤ ?a → 1 / ?a ≤ -1
one_div_lt_neg_one|?a < 0 → -1 < ?a → 1 / ?a < -1
one_div_mul_cancel|?a ≠ 0 → 1 / ?a * ?a = 1
one_div_mul_one_div'|∀ (a b : ?A), 1 / a * (1 / b) = 1 / (b * a)
one_div_mul_one_div|∀ (a b : ?A), 1 / a * (1 / b) = 1 / (a * b)
one_div_ne_zero|?a ≠ 0 → 1 / ?a ≠ 0
one_div_neg_of_neg|?a < 0 → 1 / ?a < 0
one_div_one_div|∀ (a : ?A), 1 / (1 / a) = a
one_div_one|1 / 1 = 1
one_div_pos_of_pos|0 < ?a → 0 < 1 / ?a
one_div_zero|1 / 0 = 0
one_dvd|∀ (a : ?A), 1 ∣ a
one_inv_eq|1⁻¹ = 1
one_inv|1⁻¹ = 1
one_le_div_iff_le|∀ (a : ?A) {b : ?A}, b > 0 → (1 ≤ a / b ↔ b ≤ a)
one_le_div_of_le|?b > 0 → ?b ≤ ?a → 1 ≤ ?a / ?b
one_le_one_div|0 < ?a → ?a ≤ 1 → 1 ≤ 1 / ?a
one_lt_div_iff_lt|∀ (a : ?A) {b : ?A}, b > 0 → (1 < a / b ↔ b < a)
one_lt_div_of_lt|?b > 0 → ?b < ?a → 1 < ?a / ?b
one_lt_one_div|0 < ?a → ?a < 1 → 1 < 1 / ?a
one_mul|∀ (a : ?A), 1 * a = a
one_nmul|∀ (a : ?A), 1⬝a = a
one_pow|∀ (n : ℕ), 1 ^ n = 1
one|?A
option.cases_on|Π (n : option ?A), ?C option.none → (Π (a : ?A), ?C (option.some a)) → ?C n
option.induction_on|Π (n : option ?A), ?C option.none → (Π (a : ?A), ?C (option.some a)) → ?C n
option.is_inhabited|Π (A : Type), inhabited (option A)
option.is_none_none|option.is_none option.none
option.is_none|option ?A → Prop
option.measurable|Π (A : Type) [_inst_1 : measurable A], measurable (option A)
option.no_confusion|?v1 = ?v2 → option.no_confusion_type ?P ?v1 ?v2
option.none_ne_some|∀ (a : ?A), option.none ≠ option.some a
option.none|option ?A
option.rec_on|Π (n : option ?A), ?C option.none → (Π (a : ?A), ?C (option.some a)) → ?C n
option.rec|?C option.none → (Π (a : ?A), ?C (option.some a)) → (Π (n : option ?A), ?C n)
option.some.inj|option.some ?a₁ = option.some ?a₂ → ?a₁ = ?a₂
option.some|?A → option ?A
option|Type → Type
or.assoc|(?a ∨ ?b) ∨ ?c ↔ ?a ∨ ?b ∨ ?c
or.by_cases|?p ∨ ?q → (?p → ?A) → (?q → ?A) → ?A
or.cases_on|?a ∨ ?b → (?a → ?C) → (?b → ?C) → ?C
or.comm|?a ∨ ?b ↔ ?b ∨ ?a
or.elim3|?a ∨ ?b ∨ ?c → (?a → ?d) → (?b → ?d) → (?c → ?d) → ?d
or.elim|?a ∨ ?b → (?a → ?c) → (?b → ?c) → ?c
or.imp_distrib|?a ∨ ?b → ?c ↔ (?a → ?c) ∧ (?b → ?c)
or.imp_left|(?a → ?b) → ?a ∨ ?c → ?b ∨ ?c
or.imp_right|(?a → ?b) → ?c ∨ ?a → ?c ∨ ?b
or.imp|(?a → ?c) → (?b → ?d) → ?a ∨ ?b → ?c ∨ ?d
or.induction_on|?a ∨ ?b → (?a → ?C) → (?b → ?C) → ?C
or.inl|?a → ?a ∨ ?b
or.inr|?b → ?a ∨ ?b
or.intro_left|Π (b : Prop), ?a → ?a ∨ b
or.intro_right|∀ (a : Prop) {b : Prop}, b → a ∨ b
or.left_comm|?a ∨ ?b ∨ ?c ↔ ?b ∨ ?a ∨ ?c
or.left_distrib|∀ (a b c : Prop), a ∨ b ∧ c ↔ (a ∨ b) ∧ (a ∨ c)
or.neg_resolve_left|¬?a ∨ ?b → ?a → ?b
or.neg_resolve_right|?a ∨ ¬?b → ?b → ?a
or.rec_on|?a ∨ ?b → (?a → ?C) → (?b → ?C) → ?C
or.rec|(?a → ?C) → (?b → ?C) → ?a ∨ ?b → ?C
or.resolve_left|?a ∨ ?b → ¬?a → ?b
or.resolve_right|?a ∨ ?b → ¬?b → ?a
or.right_comm|∀ (a b c : Prop), (a ∨ b) ∨ c ↔ (a ∨ c) ∨ b
or.right_distrib|∀ (a b c : Prop), a ∧ b ∨ c ↔ (a ∨ c) ∧ (b ∨ c)
or.swap|?a ∨ ?b → ?b ∨ ?a
or_congr|(?a ↔ ?c) → (?b ↔ ?d) → (?a ∨ ?b ↔ ?c ∨ ?d)
or_false|∀ (a : Prop), a ∨ false ↔ a
or_iff_left_of_imp|(?b → ?a) → (?a ∨ ?b ↔ ?a)
or_iff_not_and_not|∀ (a b : Prop) [Da : decidable a] [Db : decidable b], a ∨ b ↔ ¬(¬a ∧ ¬b)
or_iff_or|(?a ↔ ?c) → (?b ↔ ?d) → (?a ∨ ?b ↔ ?c ∨ ?d)
or_iff_right_of_imp|(?a → ?b) → (?a ∨ ?b ↔ ?b)
or_not_self_iff|∀ (a : Prop) [D : decidable a], a ∨ ¬a ↔ true
or_of_or_of_imp_left|?a ∨ ?c → (?a → ?b) → ?b ∨ ?c
or_resolve_left|?a ∨ ?b → ¬?b → ?a
or_resolve_right|?a ∨ ?b → ¬?a → ?b
or_self|∀ (a : Prop), a ∨ a ↔ a
or_true|∀ (a : Prop), a ∨ true ↔ true
order_pair._trans_of_to_weak_order|Π (A : Type) [s : order_pair A], has_le A
order_pair.cases_on|Π (n : order_pair ?A), (Π (le : ?A → ?A → Prop) (le_refl : ∀ (a : ?A), le a a) (le_trans : ∀ (a b c : ?A), le a b → le b c → le a c) (le_antisymm : ∀ (a b : ?A), le a b → le b a → a = b) (lt : ?A → ?A → Prop) (le_of_lt : ∀ (a b : ?A), lt a b → le a b) (lt_of_lt_of_le : ∀ (a b c : ?A), lt a b → le b c → lt a c) (lt_of_le_of_lt : ∀ (a b c : ?A), le a b → lt b c → lt a c) (lt_irrefl : ∀ (a : ?A), ¬lt a a), ?C (order_pair.mk le le_refl le_trans le_antisymm lt le_of_lt lt_of_lt_of_le lt_of_le_of_lt lt_irrefl)) → ?C n
order_pair.destruct|Π (n : order_pair ?A), (Π (le : ?A → ?A → Prop) (le_refl : ∀ (a : ?A), le a a) (le_trans : ∀ (a b c : ?A), le a b → le b c → le a c) (le_antisymm : ∀ (a b : ?A), le a b → le b a → a = b) (lt : ?A → ?A → Prop) (le_of_lt : ∀ (a b : ?A), lt a b → le a b) (lt_of_lt_of_le : ∀ (a b c : ?A), lt a b → le b c → lt a c) (lt_of_le_of_lt : ∀ (a b c : ?A), le a b → lt b c → lt a c) (lt_irrefl : ∀ (a : ?A), ¬lt a a), ?C (order_pair.mk le le_refl le_trans le_antisymm lt le_of_lt lt_of_lt_of_le lt_of_le_of_lt lt_irrefl)) → ?C n
order_pair.mk|Π (le : ?A → ?A → Prop), (∀ (a : ?A), le a a) → (∀ (a b c : ?A), le a b → le b c → le a c) → (∀ (a b : ?A), le a b → le b a → a = b) → (Π (lt : ?A → ?A → Prop), (∀ (a b : ?A), lt a b → le a b) → (∀ (a b c : ?A), lt a b → le b c → lt a c) → (∀ (a b c : ?A), le a b → lt b c → lt a c) → (∀ (a : ?A), ¬lt a a) → order_pair ?A)
order_pair.rec_on|Π (n : order_pair ?A), (Π (le : ?A → ?A → Prop) (le_refl : ∀ (a : ?A), le a a) (le_trans : ∀ (a b c : ?A), le a b → le b c → le a c) (le_antisymm : ∀ (a b : ?A), le a b → le b a → a = b) (lt : ?A → ?A → Prop) (le_of_lt : ∀ (a b : ?A), lt a b → le a b) (lt_of_lt_of_le : ∀ (a b c : ?A), lt a b → le b c → lt a c) (lt_of_le_of_lt : ∀ (a b c : ?A), le a b → lt b c → lt a c) (lt_irrefl : ∀ (a : ?A), ¬lt a a), ?C (order_pair.mk le le_refl le_trans le_antisymm lt le_of_lt lt_of_lt_of_le lt_of_le_of_lt lt_irrefl)) → ?C n
order_pair.rec|(Π (le : ?A → ?A → Prop) (le_refl : ∀ (a : ?A), le a a) (le_trans : ∀ (a b c : ?A), le a b → le b c → le a c) (le_antisymm : ∀ (a b : ?A), le a b → le b a → a = b) (lt : ?A → ?A → Prop) (le_of_lt : ∀ (a b : ?A), lt a b → le a b) (lt_of_lt_of_le : ∀ (a b c : ?A), lt a b → le b c → lt a c) (lt_of_le_of_lt : ∀ (a b c : ?A), le a b → lt b c → lt a c) (lt_irrefl : ∀ (a : ?A), ¬lt a a), ?C (order_pair.mk le le_refl le_trans le_antisymm lt le_of_lt lt_of_lt_of_le lt_of_le_of_lt lt_irrefl)) → (Π (n : order_pair ?A), ?C n)
order_pair.to_weak_order|Π (A : Type) [s : order_pair A], weak_order A
order_pair|Type → Type
ordered_cancel_comm_monoid.destruct|Π (n : ordered_cancel_comm_monoid ?A), (Π (add : ?A → ?A → ?A) (add_assoc : ∀ (a b c : ?A), add (add a b) c = add a (add b c)) (zero : ?A) (zero_add : ∀ (a : ?A), add zero a = a) (add_zero : ∀ (a : ?A), add a zero = a) (add_comm : ∀ (a b : ?A), add a b = add b a) (add_left_cancel : ∀ (a b c : ?A), add a b = add a c → b = c) (add_right_cancel : ∀ (a b c : ?A), add a b = add c b → a = c) (le : ?A → ?A → Prop) (le_refl : ∀ (a : ?A), le a a) (le_trans : ∀ (a b c : ?A), le a b → le b c → le a c) (le_antisymm : ∀ (a b : ?A), le a b → le b a → a = b) (lt : ?A → ?A → Prop) (le_of_lt : ∀ (a b : ?A), lt a b → le a b) (lt_of_lt_of_le : ∀ (a b c : ?A), lt a b → le b c → lt a c) (lt_of_le_of_lt : ∀ (a b c : ?A), le a b → lt b c → lt a c) (lt_irrefl : ∀ (a : ?A), ¬lt a a) (add_le_add_left : Π (a b : ?A), le a b → (∀ (c : ?A), le (add c a) (add c b))) (le_of_add_le_add_left : ∀ (a b c : ?A), le (add a b) (add a c) → le b c) (add_lt_add_left : Π (a b : ?A), lt a b → (∀ (c : ?A), lt (add c a) (add c b))) (lt_of_add_lt_add_left : ∀ (a b c : ?A), lt (add a b) (add a c) → lt b c), ?C (ordered_cancel_comm_monoid.mk add add_assoc zero zero_add add_zero add_comm add_left_cancel add_right_cancel le le_refl le_trans le_antisymm lt le_of_lt lt_of_lt_of_le lt_of_le_of_lt lt_irrefl add_le_add_left le_of_add_le_add_left add_lt_add_left lt_of_add_lt_add_left)) → ?C n
ordered_cancel_comm_monoid.mk|Π (add : ?A → ?A → ?A), (∀ (a b c : ?A), add (add a b) c = add a (add b c)) → (Π (zero : ?A), (∀ (a : ?A), add zero a = a) → (∀ (a : ?A), add a zero = a) → (∀ (a b : ?A), add a b = add b a) → (∀ (a b c : ?A), add a b = add a c → b = c) → (∀ (a b c : ?A), add a b = add c b → a = c) → (Π (le : ?A → ?A → Prop), (∀ (a : ?A), le a a) → (∀ (a b c : ?A), le a b → le b c → le a c) → (∀ (a b : ?A), le a b → le b a → a = b) → (Π (lt : ?A → ?A → Prop), (∀ (a b : ?A), lt a b → le a b) → (∀ (a b c : ?A), lt a b → le b c → lt a c) → (∀ (a b c : ?A), le a b → lt b c → lt a c) → (∀ (a : ?A), ¬lt a a) → (Π (a b : ?A), le a b → (∀ (c : ?A), le (add c a) (add c b))) → (∀ (a b c : ?A), le (add a b) (add a c) → le b c) → (Π (a b : ?A), lt a b → (∀ (c : ?A), lt (add c a) (add c b))) → (∀ (a b c : ?A), lt (add a b) (add a c) → lt b c) → ordered_cancel_comm_monoid ?A)))
ordered_comm_group.mk|Π (add : ?A → ?A → ?A), (∀ (a b c : ?A), add (add a b) c = add a (add b c)) → (Π (zero : ?A), (∀ (a : ?A), add zero a = a) → (∀ (a : ?A), add a zero = a) → (Π (neg : ?A → ?A), (∀ (a : ?A), add (neg a) a = zero) → (∀ (a b : ?A), add a b = add b a) → (Π (le : ?A → ?A → Prop), (∀ (a : ?A), le a a) → (∀ (a b c : ?A), le a b → le b c → le a c) → (∀ (a b : ?A), le a b → le b a → a = b) → (Π (lt : ?A → ?A → Prop), (∀ (a b : ?A), lt a b → le a b) → (∀ (a b c : ?A), lt a b → le b c → lt a c) → (∀ (a b c : ?A), le a b → lt b c → lt a c) → (∀ (a : ?A), ¬lt a a) → (Π (a b : ?A), le a b → (∀ (c : ?A), le (add c a) (add c b))) → (Π (a b : ?A), lt a b → (∀ (c : ?A), lt (add c a) (add c b))) → ordered_comm_group ?A))))
ordered_comm_group|Type → Type
ordered_ring._trans_of_to_ordered_comm_group_16|Π (A : Type) [s : ordered_ring A], add_comm_group A
ordered_ring._trans_of_to_ordered_comm_group_7|Π (A : Type) [s : ordered_ring A], add_semigroup A
ordered_ring._trans_of_to_ordered_semiring_8|order_pair ?A
ordered_ring._trans_of_to_zero_ne_one_class_1|Π (A : Type) [s : ordered_ring A], has_zero A
ordered_ring.mk|Π (add : ?A → ?A → ?A), (∀ (a b c : ?A), add (add a b) c = add a (add b c)) → (Π (zero : ?A), (∀ (a : ?A), add zero a = a) → (∀ (a : ?A), add a zero = a) → (Π (neg : ?A → ?A), (∀ (a : ?A), add (neg a) a = zero) → (∀ (a b : ?A), add a b = add b a) → (Π (mul : ?A → ?A → ?A), (∀ (a b c : ?A), mul (mul a b) c = mul a (mul b c)) → (Π (one : ?A), (∀ (a : ?A), mul one a = a) → (∀ (a : ?A), mul a one = a) → (∀ (a b c : ?A), mul a (add b c) = add (mul a b) (mul a c)) → (∀ (a b c : ?A), mul (add a b) c = add (mul a c) (mul b c)) → (Π (le : ?A → ?A → Prop), (∀ (a : ?A), le a a) → (∀ (a b c : ?A), le a b → le b c → le a c) → (∀ (a b : ?A), le a b → le b a → a = b) → (Π (lt : ?A → ?A → Prop), (∀ (a b : ?A), lt a b → le a b) → (∀ (a b c : ?A), lt a b → le b c → lt a c) → (∀ (a b c : ?A), le a b → lt b c → lt a c) → (∀ (a : ?A), ¬lt a a) → (Π (a b : ?A), le a b → (∀ (c : ?A), le (add c a) (add c b))) → (Π (a b : ?A), lt a b → (∀ (c : ?A), lt (add c a) (add c b))) → zero ≠ one → (∀ (a b : ?A), le zero a → le zero b → le zero (mul a b)) → (∀ (a b : ?A), lt zero a → lt zero b → lt zero (mul a b)) → ordered_ring ?A))))))
ordered_ring.rec_on|Π (n : ordered_ring ?A), (Π (add : ?A → ?A → ?A) (add_assoc : ∀ (a b c : ?A), add (add a b) c = add a (add b c)) (zero : ?A) (zero_add : ∀ (a : ?A), add zero a = a) (add_zero : ∀ (a : ?A), add a zero = a) (neg : ?A → ?A) (add_left_inv : ∀ (a : ?A), add (neg a) a = zero) (add_comm : ∀ (a b : ?A), add a b = add b a) (mul : ?A → ?A → ?A) (mul_assoc : ∀ (a b c : ?A), mul (mul a b) c = mul a (mul b c)) (one : ?A) (one_mul : ∀ (a : ?A), mul one a = a) (mul_one : ∀ (a : ?A), mul a one = a) (left_distrib : ∀ (a b c : ?A), mul a (add b c) = add (mul a b) (mul a c)) (right_distrib : ∀ (a b c : ?A), mul (add a b) c = add (mul a c) (mul b c)) (le : ?A → ?A → Prop) (le_refl : ∀ (a : ?A), le a a) (le_trans : ∀ (a b c : ?A), le a b → le b c → le a c) (le_antisymm : ∀ (a b : ?A), le a b → le b a → a = b) (lt : ?A → ?A → Prop) (le_of_lt : ∀ (a b : ?A), lt a b → le a b) (lt_of_lt_of_le : ∀ (a b c : ?A), lt a b → le b c → lt a c) (lt_of_le_of_lt : ∀ (a b c : ?A), le a b → lt b c → lt a c) (lt_irrefl : ∀ (a : ?A), ¬lt a a) (add_le_add_left : Π (a b : ?A), le a b → (∀ (c : ?A), le (add c a) (add c b))) (add_lt_add_left : Π (a b : ?A), lt a b → (∀ (c : ?A), lt (add c a) (add c b))) (zero_ne_one : zero ≠ one) (mul_nonneg : ∀ (a b : ?A), le zero a → le zero b → le zero (mul a b)) (mul_pos : ∀ (a b : ?A), lt zero a → lt zero b → lt zero (mul a b)), ?C (ordered_ring.mk add add_assoc zero zero_add add_zero neg add_left_inv add_comm mul mul_assoc one one_mul mul_one left_distrib right_distrib le le_refl le_trans le_antisymm lt le_of_lt lt_of_lt_of_le lt_of_le_of_lt lt_irrefl add_le_add_left add_lt_add_left zero_ne_one mul_nonneg mul_pos)) → ?C n
ordered_ring.rec|(Π (add : ?A → ?A → ?A) (add_assoc : ∀ (a b c : ?A), add (add a b) c = add a (add b c)) (zero : ?A) (zero_add : ∀ (a : ?A), add zero a = a) (add_zero : ∀ (a : ?A), add a zero = a) (neg : ?A → ?A) (add_left_inv : ∀ (a : ?A), add (neg a) a = zero) (add_comm : ∀ (a b : ?A), add a b = add b a) (mul : ?A → ?A → ?A) (mul_assoc : ∀ (a b c : ?A), mul (mul a b) c = mul a (mul b c)) (one : ?A) (one_mul : ∀ (a : ?A), mul one a = a) (mul_one : ∀ (a : ?A), mul a one = a) (left_distrib : ∀ (a b c : ?A), mul a (add b c) = add (mul a b) (mul a c)) (right_distrib : ∀ (a b c : ?A), mul (add a b) c = add (mul a c) (mul b c)) (le : ?A → ?A → Prop) (le_refl : ∀ (a : ?A), le a a) (le_trans : ∀ (a b c : ?A), le a b → le b c → le a c) (le_antisymm : ∀ (a b : ?A), le a b → le b a → a = b) (lt : ?A → ?A → Prop) (le_of_lt : ∀ (a b : ?A), lt a b → le a b) (lt_of_lt_of_le : ∀ (a b c : ?A), lt a b → le b c → lt a c) (lt_of_le_of_lt : ∀ (a b c : ?A), le a b → lt b c → lt a c) (lt_irrefl : ∀ (a : ?A), ¬lt a a) (add_le_add_left : Π (a b : ?A), le a b → (∀ (c : ?A), le (add c a) (add c b))) (add_lt_add_left : Π (a b : ?A), lt a b → (∀ (c : ?A), lt (add c a) (add c b))) (zero_ne_one : zero ≠ one) (mul_nonneg : ∀ (a b : ?A), le zero a → le zero b → le zero (mul a b)) (mul_pos : ∀ (a b : ?A), lt zero a → lt zero b → lt zero (mul a b)), ?C (ordered_ring.mk add add_assoc zero zero_add add_zero neg add_left_inv add_comm mul mul_assoc one one_mul mul_one left_distrib right_distrib le le_refl le_trans le_antisymm lt le_of_lt lt_of_lt_of_le lt_of_le_of_lt lt_irrefl add_le_add_left add_lt_add_left zero_ne_one mul_nonneg mul_pos)) → (Π (n : ordered_ring ?A), ?C n)
ordered_ring|Type → Type
ordered_semiring.mk|Π (add : ?A → ?A → ?A), (∀ (a b c : ?A), add (add a b) c = add a (add b c)) → (Π (zero : ?A), (∀ (a : ?A), add zero a = a) → (∀ (a : ?A), add a zero = a) → (∀ (a b : ?A), add a b = add b a) → (Π (mul : ?A → ?A → ?A), (∀ (a b c : ?A), mul (mul a b) c = mul a (mul b c)) → (Π (one : ?A), (∀ (a : ?A), mul one a = a) → (∀ (a : ?A), mul a one = a) → (∀ (a b c : ?A), mul a (add b c) = add (mul a b) (mul a c)) → (∀ (a b c : ?A), mul (add a b) c = add (mul a c) (mul b c)) → (∀ (a : ?A), mul zero a = zero) → (∀ (a : ?A), mul a zero = zero) → (∀ (a b c : ?A), add a b = add a c → b = c) → (∀ (a b c : ?A), add a b = add c b → a = c) → (Π (le : ?A → ?A → Prop), (∀ (a : ?A), le a a) → (∀ (a b c : ?A), le a b → le b c → le a c) → (∀ (a b : ?A), le a b → le b a → a = b) → (Π (lt : ?A → ?A → Prop), (∀ (a b : ?A), lt a b → le a b) → (∀ (a b c : ?A), lt a b → le b c → lt a c) → (∀ (a b c : ?A), le a b → lt b c → lt a c) → (∀ (a : ?A), ¬lt a a) → (Π (a b : ?A), le a b → (∀ (c : ?A), le (add c a) (add c b))) → (∀ (a b c : ?A), le (add a b) (add a c) → le b c) → (Π (a b : ?A), lt a b → (∀ (c : ?A), lt (add c a) (add c b))) → (∀ (a b c : ?A), lt (add a b) (add a c) → lt b c) → (∀ (a b c : ?A), le a b → le zero c → le (mul c a) (mul c b)) → (∀ (a b c : ?A), le a b → le zero c → le (mul a c) (mul b c)) → (∀ (a b c : ?A), lt a b → lt zero c → lt (mul c a) (mul c b)) → (∀ (a b c : ?A), lt a b → lt zero c → lt (mul a c) (mul b c)) → ordered_semiring ?A)))))
ordered_semiring.rec|(Π (add : ?A → ?A → ?A) (add_assoc : ∀ (a b c : ?A), add (add a b) c = add a (add b c)) (zero : ?A) (zero_add : ∀ (a : ?A), add zero a = a) (add_zero : ∀ (a : ?A), add a zero = a) (add_comm : ∀ (a b : ?A), add a b = add b a) (mul : ?A → ?A → ?A) (mul_assoc : ∀ (a b c : ?A), mul (mul a b) c = mul a (mul b c)) (one : ?A) (one_mul : ∀ (a : ?A), mul one a = a) (mul_one : ∀ (a : ?A), mul a one = a) (left_distrib : ∀ (a b c : ?A), mul a (add b c) = add (mul a b) (mul a c)) (right_distrib : ∀ (a b c : ?A), mul (add a b) c = add (mul a c) (mul b c)) (zero_mul : ∀ (a : ?A), mul zero a = zero) (mul_zero : ∀ (a : ?A), mul a zero = zero) (add_left_cancel : ∀ (a b c : ?A), add a b = add a c → b = c) (add_right_cancel : ∀ (a b c : ?A), add a b = add c b → a = c) (le : ?A → ?A → Prop) (le_refl : ∀ (a : ?A), le a a) (le_trans : ∀ (a b c : ?A), le a b → le b c → le a c) (le_antisymm : ∀ (a b : ?A), le a b → le b a → a = b) (lt : ?A → ?A → Prop) (le_of_lt : ∀ (a b : ?A), lt a b → le a b) (lt_of_lt_of_le : ∀ (a b c : ?A), lt a b → le b c → lt a c) (lt_of_le_of_lt : ∀ (a b c : ?A), le a b → lt b c → lt a c) (lt_irrefl : ∀ (a : ?A), ¬lt a a) (add_le_add_left : Π (a b : ?A), le a b → (∀ (c : ?A), le (add c a) (add c b))) (le_of_add_le_add_left : ∀ (a b c : ?A), le (add a b) (add a c) → le b c) (add_lt_add_left : Π (a b : ?A), lt a b → (∀ (c : ?A), lt (add c a) (add c b))) (lt_of_add_lt_add_left : ∀ (a b c : ?A), lt (add a b) (add a c) → lt b c) (mul_le_mul_of_nonneg_left : ∀ (a b c : ?A), le a b → le zero c → le (mul c a) (mul c b)) (mul_le_mul_of_nonneg_right : ∀ (a b c : ?A), le a b → le zero c → le (mul a c) (mul b c)) (mul_lt_mul_of_pos_left : ∀ (a b c : ?A), lt a b → lt zero c → lt (mul c a) (mul c b)) (mul_lt_mul_of_pos_right : ∀ (a b c : ?A), lt a b → lt zero c → lt (mul a c) (mul b c)), ?C (ordered_semiring.mk add add_assoc zero zero_add add_zero add_comm mul mul_assoc one one_mul mul_one left_distrib right_distrib zero_mul mul_zero add_left_cancel add_right_cancel le le_refl le_trans le_antisymm lt le_of_lt lt_of_lt_of_le lt_of_le_of_lt lt_irrefl add_le_add_left le_of_add_le_add_left add_lt_add_left lt_of_add_lt_add_left mul_le_mul_of_nonneg_left mul_le_mul_of_nonneg_right mul_lt_mul_of_pos_left mul_lt_mul_of_pos_right)) → (Π (n : ordered_semiring ?A), ?C n)
ordered_semiring|Type → Type
or|Prop → Prop → Prop
pair|?A → ?B → ?A × ?B
peirce|∀ (a b : Prop) [D : decidable a], ((a → b) → a) → a
perm.eqv|∀ (A : Type), equivalence perm
perm.nil|perm list.nil list.nil
perm.perm_app|perm ?l₁ ?l₂ → perm ?t₁ ?t₂ → perm (list.append ?l₁ ?t₁) (list.append ?l₂ ?t₂)
perm.perm_rev|∀ (l : list ?A), perm l (list.reverse l)
perm.rec_on|perm ?a ?a → ?C list.nil list.nil → (Π (x : ?A) {l₁ l₂ : list ?A}, perm l₁ l₂ → ?C l₁ l₂ → ?C (list.cons x l₁) (list.cons x l₂)) → (Π (x y : ?A) (l : list ?A), ?C (list.cons y (list.cons x l)) (list.cons x (list.cons y l))) → (Π {l₁ l₂ l₃ : list ?A}, perm l₁ l₂ → perm l₂ l₃ → ?C l₁ l₂ → ?C l₂ l₃ → ?C l₁ l₃) → ?C ?a ?a
perm.rec|?C list.nil list.nil → (Π (x : ?A) {l₁ l₂ : list ?A}, perm l₁ l₂ → ?C l₁ l₂ → ?C (list.cons x l₁) (list.cons x l₂)) → (Π (x y : ?A) (l : list ?A), ?C (list.cons y (list.cons x l)) (list.cons x (list.cons y l))) → (Π {l₁ l₂ l₃ : list ?A}, perm l₁ l₂ → perm l₂ l₃ → ?C l₁ l₂ → ?C l₂ l₃ → ?C l₁ l₃) → (Π {a a_1 : list ?A}, perm a a_1 → ?C a a_1)
perm.refl|∀ (l : list ?A), perm l l
perm.skip|∀ (x : ?A) {l₁ l₂ : list ?A}, perm l₁ l₂ → perm (list.cons x l₁) (list.cons x l₂)
perm.swap|∀ (x y : ?A) (l : list ?A), perm (list.cons y (list.cons x l)) (list.cons x (list.cons y l))
perm.symm|perm ?l₁ ?l₂ → perm ?l₂ ?l₁
perm.trans|perm ?l₁ ?l₂ → perm ?l₂ ?l₃ → perm ?l₁ ?l₃
perm.xswap|∀ (x y : ?A), perm ?l₁ ?l₂ → perm (list.cons x (list.cons y ?l₁)) (list.cons y (list.cons x ?l₂))
perm|list ?A → list ?A → Prop
pi_eq|?P = ?P' → (Π (x : ?A), ?P x) = Π (x : ?A), ?P' x
pnat.add|pnat.pnat → pnat.pnat → pnat.pnat
pnat.inv_cancel_left|∀ (p : pnat.pnat), pnat.rat_of_pnat p * pnat.inv p = 1
pnat.inv_le_one|∀ (n : pnat.pnat), pnat.inv n ≤ 1
pnat.inv_pos|∀ (n : pnat.pnat), pnat.inv n > 0
pnat.inv_two_mul_lt_inv|∀ (n : pnat.pnat), pnat.inv (subtype.tag 2 dec_trivial * n) < pnat.inv n
pnat.inv|pnat.pnat → ℚ
pnat.le_def|∀ (p q : pnat.pnat), p ≤ q = (pnat.nat_of_pnat p ≤ pnat.nat_of_pnat q)
pnat.le_refl|∀ (a : pnat.pnat), a ≤ a
pnat.le_trans|?p ≤ ?q → ?q ≤ ?r → ?p ≤ ?r
pnat.le|pnat.pnat → pnat.pnat → Prop
pnat.lt_def|∀ (p q : pnat.pnat), p < q = (pnat.nat_of_pnat p < pnat.nat_of_pnat q)
pnat.lt|pnat.pnat → pnat.pnat → Prop
pnat.max_left|∀ (a b : pnat.pnat), pnat.max a b ≥ a
pnat.max|pnat.pnat → pnat.pnat → pnat.pnat
pnat.mul_comm|∀ (a b : pnat.pnat), a * b = b * a
pnat.mul_def|∀ (p q : pnat.pnat), p * q = subtype.tag (pnat.nat_of_pnat p * pnat.nat_of_pnat q) (mul_pos (pnat.pnat_pos p) (pnat.pnat_pos q))
pnat.mul|pnat.pnat → pnat.pnat → pnat.pnat
pnat.one_mul|∀ (n : pnat.pnat), pnat.pone * n = n
pnat.pceil|ℚ → pnat.pnat
pnat.pnat.eq|pnat.nat_of_pnat ?p = pnat.nat_of_pnat ?q → ?p = ?q
pnat.pnat|Type₁
pnat.pone_le|∀ (n : pnat.pnat), pnat.pone ≤ n
pnat.pone|pnat.pnat
pnat.pos|Π (n : ℕ), n > 0 → pnat.pnat
pnat.two_mul|∀ (p : pnat.pnat), pnat.rat_of_pnat (subtype.tag 2 dec_trivial * p) = (1 + 1) * pnat.rat_of_pnat p
poly_unit|Type
pos_and_pos_or_neg_and_neg_of_mul_pos|?a * ?b > 0 → ?a > 0 ∧ ?b > 0 ∨ ?a < 0 ∧ ?b < 0
pos_num.add|pos_num → pos_num → pos_num
pos_num.below|pos_num → Type
pos_num.bit0|pos_num → pos_num
pos_num.bit1|pos_num → pos_num
pos_num.le|pos_num → pos_num → bool
pos_num.lt|pos_num → pos_num → bool
pos_num.mul|pos_num → pos_num → pos_num
pos_num.one_mul|∀ (a : pos_num), pos_num.one * a = a
pos_num.one|pos_num
pos_num.pred|pos_num → pos_num
pos_num.rec|?C pos_num.one → (Π (a : pos_num), ?C a → ?C (pos_num.bit1 a)) → (Π (a : pos_num), ?C a → ?C (pos_num.bit0 a)) → (Π (n : pos_num), ?C n)
pos_num.size|pos_num → pos_num
pos_num.succ|pos_num → pos_num
pos_num|Type₁
pos_of_sign_eq_one|sign ?a = 1 → ?a > 0
pow_add|∀ (a : ?A) (m n : ℕ), a ^ (m + n) = a ^ m * a ^ n
pow_comm|∀ (a : ?A) (m n : ℕ), a ^ m * a ^ n = a ^ n * a ^ m
pow_four|∀ (a : ?A), a ^ 4 = a * (a * (a * a))
pow_ge_one|∀ (i : ℕ), ?x ≥ 1 → ?x ^ i ≥ 1
pow_gt_one|?x > 1 → ?i > 0 → ?x ^ ?i > 1
pow_int|?A → ℤ → ?A
pow_inv_comm|∀ (a : ?A) (m n : ℕ), a⁻¹ ^ m * a ^ n = a ^ n * a⁻¹ ^ m
pow_mul|∀ (a : ?A) (m n : ℕ), a ^ (m * n) = a ^ m ^ n
pow_nat|?A → ℕ → ?A
pow_one|∀ (a : ?A), a ^ 1 = a
pow_pos|?a > 0 → (∀ (n : ℕ), ?a ^ n > 0)
pow_sub|∀ (a : ?A) {m n : ℕ}, m ≥ n → a ^ (m - n) = a ^ m * (a ^ n)⁻¹
pow_succ'|∀ (a : ?A) (n : ℕ), a ^ nat.succ n = a ^ n * a
pow_succ|∀ (a : ?A) (n : ℕ), a ^ nat.succ n = a * a ^ n
pow_three|∀ (a : ?A), a ^ 3 = a * (a * a)
pow_two_add|∀ (n : ℕ), 2 ^ n + 2 ^ n = 2 ^ nat.succ n
pow_two|∀ (a : ?A), a ^ 2 = a * a
pow_zero|∀ (a : ?A), a ^ 0 = 1
prerat.add|prerat → prerat → prerat
prerat.equiv.symm|prerat.equiv ?a ?b → prerat.equiv ?b ?a
prerat.equiv_zero_of_num_eq_zero|prerat.num ?a = 0 → prerat.equiv ?a prerat.zero
prerat.equiv|prerat → prerat → Prop
prerat.eq|prerat.num ?a = prerat.num ?b → prerat.denom ?a = prerat.denom ?b → ?a = ?b
prerat.inv|prerat → prerat
prerat.mk|ℤ → (Π (denom : ℤ), denom > 0 → prerat)
prerat.mul|prerat → prerat → prerat
prerat.neg|prerat → prerat
prerat.of_int.inj|prerat.equiv (prerat.of_int ?a) (prerat.of_int ?b) → ?a = ?b
prerat.one|prerat
prerat.pos|prerat → Prop
prerat.rec|(Π (num denom : ℤ) (denom_pos : denom > 0), ?C (prerat.mk num denom denom_pos)) → (Π (n : prerat), ?C n)
prerat.smul|Π (a : ℤ), prerat → a > 0 → prerat
prerat.zero|prerat
prerat|Type₁
prod.eq|prod.pr1 ?p₁ = prod.pr1 ?p₂ → prod.pr2 ?p₁ = prod.pr2 ?p₂ → ?p₁ = ?p₂
prod.eta|∀ (p : ?A × ?B), (prod.pr1 p, prod.pr2 p) = p
prod.lex.rec|(Π {a₁ : ?A} {b₁ : ?B} (a₂ : ?A) (b₂ : ?B), ?Ra a₁ a₂ → ?C (a₁, b₁) (a₂, b₂)) → (Π (a : ?A) {b₁ b₂ : ?B}, ?Rb b₁ b₂ → ?C (a, b₁) (a, b₂)) → (Π {a a_1 : ?A × ?B}, prod.lex ?Ra ?Rb a a_1 → ?C a a_1)
prod.lex.wf|well_founded ?Ra → well_founded ?Rb → well_founded (prod.lex ?Ra ?Rb)
prod.lex|(?A → ?A → Prop) → (?B → ?B → Prop) → ?A × ?B → ?A × ?B → Prop
prod.mk|?A → ?B → ?A × ?B
prod.pair_eq|?a₁ = ?a₂ → ?b₁ = ?b₂ → (?a₁, ?b₁) = (?a₂, ?b₂)
prod.pr1.mk|∀ (a : ?A) (b : ?B), prod.pr1 (a, b) = a
prod.pr1|?A × ?B → ?A
prod.pr2.mk|∀ (a : ?A) (b : ?B), prod.pr2 (a, b) = b
prod.pr2|?A × ?B → ?B
prod.rec_on|Π (n : ?A × ?B), (Π (a : ?A) (a_1 : ?B), ?C (a, a_1)) → ?C n
prod.rec|(Π (a : ?A) (a_1 : ?B), ?C (a, a_1)) → (Π (n : ?A × ?B), ?C n)
prod.rprod.sub_lex|∀ (a b : ?A × ?B), prod.rprod ?Ra ?Rb a b → prod.lex ?Ra ?Rb a b
prod.rprod.wf|well_founded ?Ra → well_founded ?Rb → well_founded (prod.rprod ?Ra ?Rb)
prod.rprod|(?A → ?A → Prop) → (?B → ?B → Prop) → ?A × ?B → ?A × ?B → Prop
prod.swap_swap|∀ (p : ?A × ?A), prod.swap (prod.swap p) = p
prod.swap|?A × ?A → ?A × ?A
prod|Type → Type → Type
proof_irrel|∀ (H₁ H₂ : ?a), H₁ = H₂
propext|(?a ↔ ?b) → ?a = ?b
quot.exact|quot.mk ?a = quot.mk ?b → setoid.r ?a ?b
quot.exists_rep|∀ (q : quot ?s), ∃ (a : ?A), quot.mk a = q
quot.has_decidable_eq|decidable_eq (quot ?s)
quot.hrec_on|Π (q : quot ?s) (f : Π (a : ?A), ?B (quot.mk a)), (∀ (a b : ?A), setoid.r a b → f a == f b) → ?B q
quot.hrec_on₂|Π (q₁ : quot ?s₁) (q₂ : quot ?s₂) (f : Π (a : ?A) (b : ?B), ?C (quot.mk a) (quot.mk b)), (∀ (a₁ : ?A) (a₂ : ?B) (b₁ : ?A) (b₂ : ?B), setoid.r a₁ b₁ → setoid.r a₂ b₂ → f a₁ a₂ == f b₁ b₂) → ?C q₁ q₂
quot.ind_beta|∀ (p : Π (a : ?A), ?B (quot.mk a)) (a : ?A), quot.ind p (quot.mk a) = p a
quot.indep_coherent|Π (f : Π (a : ?A), ?B (quot.mk a)), (∀ (a b : ?A) (p : setoid.r a b), eq.rec (f a) (quot.sound p) = f b) → (∀ (a b : ?A), setoid.r a b → quot.indep f a = quot.indep f b)
quot.indep|(Π (a : ?A), ?B (quot.mk a)) → ?A → sigma ?B
quot.induction_on|Π (q : quot ?s), (Π (a : ?A), ?B (quot.mk a)) → ?B q
quot.induction_on₃|Π (q₁ : quot ?s₁) (q₂ : quot ?s₂) (q₃ : quot ?s₃), (Π (a : ?A) (b : ?B) (c : ?C), ?D (quot.mk a) (quot.mk b) (quot.mk c)) → ?D q₁ q₂ q₃
quot.induction_on₂|Π (q₁ : quot ?s₁) (q₂ : quot ?s₂), (Π (a : ?A) (b : ?B), ?C (quot.mk a) (quot.mk b)) → ?C q₁ q₂
quot.ind|(Π (a : ?A), ?B (quot.mk a)) → (Π (q : quot ?s), ?B q)
quot.ind₂|(Π (a : ?A) (b : ?B), ?C (quot.mk a) (quot.mk b)) → (Π (q₁ : quot ?s₁) (q₂ : quot ?s₂), ?C q₁ q₂)
quot.lift_beta|∀ (f : ?A → ?B) (c : ∀ (a b : ?A), setoid.r a b → f a = f b) (a : ?A), quot.lift f c (quot.mk a) = f a
quot.lift_indep_pr1|∀ (f : Π (a : ?A), ?B (quot.mk a)) (H : ∀ (a b : ?A) (p : setoid.r a b), eq.rec (f a) (quot.sound p) = f b) (q : quot ?s), sigma.pr1 (quot.lift (quot.indep f) (quot.indep_coherent f H) q) = q
quot.lift_on|quot ?s → (Π (f : ?A → ?B), (∀ (a b : ?A), setoid.r a b → f a = f b) → ?B)
quot.lift_on₂|quot ?s₁ → quot ?s₂ → (Π (f : ?A → ?B → ?C), (∀ (a₁ : ?A) (a₂ : ?B) (b₁ : ?A) (b₂ : ?B), setoid.r a₁ b₁ → setoid.r a₂ b₂ → f a₁ a₂ = f b₁ b₂) → ?C)
quot.lift|Π (f : ?A → ?B), (∀ (a b : ?A), setoid.r a b → f a = f b) → quot ?s → ?B
quot.lift₂|Π (f : ?A → ?B → ?C), (∀ (a₁ : ?A) (a₂ : ?B) (b₁ : ?A) (b₂ : ?B), setoid.r a₁ b₁ → setoid.r a₂ b₂ → f a₁ a₂ = f b₁ b₂) → quot ?s₁ → quot ?s₂ → ?C
quot.mk|?A → quot ?s
quot.rec_on_subsingleton|Π (q : quot ?s), (Π (a : ?A), ?B (quot.mk a)) → ?B q
quot.rec_on_subsingleton₂|Π (q₁ : quot ?s₁) (q₂ : quot ?s₂), (Π (a : ?A) (b : ?B), ?C (quot.mk a) (quot.mk b)) → ?C q₁ q₂
quot.rec_on|Π (q : quot ?s) (f : Π (a : ?A), ?B (quot.mk a)), (∀ (a b : ?A) (p : setoid.r a b), eq.rec (f a) (quot.sound p) = f b) → ?B q
quot.rec|Π (f : Π (a : ?A), ?B (quot.mk a)), (∀ (a b : ?A) (p : setoid.r a b), eq.rec (f a) (quot.sound p) = f b) → (Π (q : quot ?s), ?B q)
quot.sound|setoid.r ?a ?b → quot.mk ?a = quot.mk ?b
quot|setoid ?A → Type
rat.add_comm|∀ (a b : ℚ), a + b = b + a
rat.add_left_inv|∀ (a : ℚ), -a + a = 0
rat.add_zero|∀ (a : ℚ), a + 0 = a
rat.add|ℚ → ℚ → ℚ
rat.binary_bound|∀ (a : ℚ), ∃ (n : ℕ), a ≤ 2 ^ n
rat.denom_pos|∀ (a : ℚ), rat.denom a > 0
rat.denom|ℚ → ℤ
rat.inv_zero|0⁻¹ = 0
rat.inv|ℚ → ℚ
rat.le_by_cases|Π (a b : ℚ), (a ≤ b → ?P) → (b ≤ a → ?P) → ?P
rat.le_def|∀ (a b : ℚ), a ≤ b = nonneg (b - a)
rat.le_of_lt|?a < ?b → ?a ≤ ?b
rat.le_refl|∀ (a : ℚ), a ≤ a
rat.le_total|∀ (a b : ℚ), a ≤ b ∨ b ≤ a
rat.le_trans|?a ≤ ?b → ?b ≤ ?c → ?a ≤ ?c
rat.le|ℚ → ℚ → Prop
rat.lt_def|∀ (a b : ℚ), a < b = pos (b - a)
rat.lt|ℚ → ℚ → Prop
rat.mul_comm|∀ (a b : ℚ), a * b = b * a
rat.mul_one|∀ (a : ℚ), a * 1 = a
rat.mul_pos|?a > 0 → ?b > 0 → ?a * ?b > 0
rat.mul|ℚ → ℚ → ℚ
rat.neg|ℚ → ℚ
rat.num|ℚ → ℤ
rat.of_int_neg|∀ (a : ℤ), rat.of_int (-a) = -rat.of_int a
rat.of_int|ℤ → ℚ
rat.of_nat.inj|rat.of_nat ?a = rat.of_nat ?b → ?a = ?b
rat.of_nat_eq|∀ (a : ℕ), rat.of_nat a = rat.of_int (int.of_nat a)
rat.of_nat_sub|?a ≥ ?b → rat.of_nat (?a - ?b) = rat.of_nat ?a - rat.of_nat ?b
rat.of_nat|ℕ → ℚ
rat.of_num|num → ℚ
rat.one_mul|∀ (a : ℚ), 1 * a = a
rat.prio|num
rat.rat_has_zero|has_zero ℚ
rat.reduce|ℚ → prerat
rat.sub.def|∀ (a b : ℚ), a - b = a + -b
rat.sub|ℚ → ℚ → ℚ
rat.ubound|ℚ → ℕ
rat.zero_add|∀ (a : ℚ), 0 + a = a
rat_seq.K₂|(pnat.pnat → ℚ) → (pnat.pnat → ℚ) → pnat.pnat
rat_seq.abs_pos_of_nonzero|rat_seq.regular ?s → rat_seq.sep ?s rat_seq.zero → (∃ (N : pnat.pnat), ∀ (m : pnat.pnat), m ≥ N → abs (?s m) ≥ pnat.inv N)
rat_seq.abs_well_defined|rat_seq.regular ?s → rat_seq.regular ?t → rat_seq.equiv ?s ?t → rat_seq.equiv (rat_seq.s_abs ?s) (rat_seq.s_abs ?t)
rat_seq.bdd_away_of_pos|rat_seq.regular ?s → rat_seq.pos ?s → (∃ (N : pnat.pnat), ∀ (n : pnat.pnat), n ≥ N → ?s n ≥ pnat.inv N)
rat_seq.canon_2_bound_right|∀ (s t : pnat.pnat → ℚ), rat_seq.regular t → (∀ (n : pnat.pnat), abs (t n) ≤ pnat.rat_of_pnat (rat_seq.K₂ s t))
rat_seq.diff_equiv_zero_of_equiv|rat_seq.regular ?s → rat_seq.regular ?t → rat_seq.equiv ?s ?t → rat_seq.equiv (rat_seq.sadd ?s (rat_seq.sneg ?t)) rat_seq.zero
rat_seq.equiv|(pnat.pnat → ℚ) → (pnat.pnat → ℚ) → Prop
rat_seq.inv_unique|∀ (Hs : rat_seq.regular ?s), rat_seq.regular ?t → rat_seq.sep ?s rat_seq.zero → rat_seq.equiv (rat_seq.smul ?s ?t) rat_seq.one → rat_seq.equiv (rat_seq.s_inv Hs) ?t
rat_seq.le_refl|rat_seq.regular ?s → rat_seq.s_le ?s ?s
rat_seq.mul_inv|∀ (Hs : rat_seq.regular ?s), rat_seq.sep ?s rat_seq.zero → rat_seq.equiv (rat_seq.smul ?s (rat_seq.s_inv Hs)) rat_seq.one
rat_seq.nonneg_of_nonneg_equiv|rat_seq.regular ?s → rat_seq.regular ?t → rat_seq.equiv ?s ?t → rat_seq.nonneg ?s → rat_seq.nonneg ?t
rat_seq.one|pnat.pnat → ℚ
rat_seq.pos_of_bdd_away|(∃ (N : pnat.pnat), ∀ (n : pnat.pnat), n ≥ N → ?s n ≥ pnat.inv N) → rat_seq.pos ?s
rat_seq.pos|(pnat.pnat → ℚ) → Prop
rat_seq.r_abs|rat_seq.reg_seq → rat_seq.reg_seq
rat_seq.r_add_consts|∀ (a b : ℚ), rat_seq.requiv (rat_seq.radd (rat_seq.r_const a) (rat_seq.r_const b)) (rat_seq.r_const (a + b))
rat_seq.r_equiv_abs_of_ge_zero|rat_seq.r_le rat_seq.r_zero ?s → rat_seq.requiv (rat_seq.r_abs ?s) ?s
rat_seq.r_inv_zero|rat_seq.requiv (rat_seq.r_inv rat_seq.r_zero) rat_seq.r_zero
rat_seq.r_le_of_lt_or_eq|∀ (s t : rat_seq.reg_seq), rat_seq.r_lt s t ∨ rat_seq.requiv s t → rat_seq.r_le s t
rat_seq.r_le|rat_seq.reg_seq → rat_seq.reg_seq → Prop
rat_seq.r_lt|rat_seq.reg_seq → rat_seq.reg_seq → Prop
rat_seq.r_mul_inv|∀ (s : rat_seq.reg_seq), rat_seq.r_sep s rat_seq.r_zero → rat_seq.requiv (rat_seq.rmul s (rat_seq.r_inv s)) rat_seq.r_one
rat_seq.r_sep|rat_seq.reg_seq → rat_seq.reg_seq → Prop
rat_seq.r_zero_lt_one|rat_seq.r_lt rat_seq.r_zero rat_seq.r_one
rat_seq.radd|rat_seq.reg_seq → rat_seq.reg_seq → rat_seq.reg_seq
rat_seq.rmul|rat_seq.reg_seq → rat_seq.reg_seq → rat_seq.reg_seq
rat_seq.rneg|rat_seq.reg_seq → rat_seq.reg_seq
rat_seq.s_abs|(pnat.pnat → ℚ) → pnat.pnat → ℚ
rat_seq.s_inv_of_zero|∀ (Hs : rat_seq.regular ?s), ¬rat_seq.sep ?s rat_seq.zero → rat_seq.s_inv Hs = rat_seq.zero
rat_seq.s_le|(pnat.pnat → ℚ) → (pnat.pnat → ℚ) → Prop
rat_seq.s_lt|(pnat.pnat → ℚ) → (pnat.pnat → ℚ) → Prop
rat_seq.s_mul_comm|∀ (s t : pnat.pnat → ℚ), rat_seq.equiv (rat_seq.smul s t) (rat_seq.smul t s)
rat_seq.sadd|(pnat.pnat → ℚ) → (pnat.pnat → ℚ) → pnat.pnat → ℚ
rat_seq.sep_zero_of_pos|rat_seq.regular ?s → rat_seq.pos ?s → rat_seq.sep ?s rat_seq.zero
rat_seq.sep|(pnat.pnat → ℚ) → (pnat.pnat → ℚ) → Prop
rat_seq.smul|(pnat.pnat → ℚ) → (pnat.pnat → ℚ) → pnat.pnat → ℚ
rat_seq.sneg|(pnat.pnat → ℚ) → pnat.pnat → ℚ
rat_seq.zero|pnat.pnat → ℚ
rat|Type₁
real._trans_of_ordered_ring_26|ordered_comm_group real
real.add_zero|∀ (x : real), x + 0 = x
real.add|real → real → real
real.approx|real → pnat.pnat → ℚ
real.cauchy_with_rate_of_converges_to_with_rate|real.converges_to_with_rate ?X ?a ?N → real.cauchy_with_rate ?X (λ (k : pnat.pnat), ?N (2 * k))
real.ceil|real → ℤ
real.dec_lt|decidable_rel real.lt
real.div|real → real → real
real.eq_zero_of_nonneg_of_forall_le|?x ≥ 0 → (∀ (ε : real), ε > 0 → ?x ≤ ε) → ?x = 0
real.eq_zero_of_nonneg_of_forall_lt|?x ≥ 0 → (∀ (ε : real), ε > 0 → ?x < ε) → ?x = 0
real.ex_rat_pos_lower_bound_of_pos|?x > 0 → (∃ (q : ℚ), q > 0 ∧ real.of_rat q ≤ ?x)
real.exists_is_sup_of_inh_of_bdd|∀ (X : real → Prop) (elt : real), X elt → (∀ (bound : real), real.ub X bound → Exists (real.is_sup X))
real.floor|real → ℤ
real.inv_mul_cancel'|∀ (x : real), real.sep x 0 → x⁻¹ * x = 1
real.inv_zero|0⁻¹ = 0
real.inv|real → real
real.is_inf|(real → Prop) → real → Prop
real.is_sup|(real → Prop) → real → Prop
real.lb|(real → Prop) → real → Prop
real.le_ceil|∀ (x : real), x ≤ real.of_int (real.ceil x)
real.le_refl|∀ (x : real), x ≤ x
real.le_total|∀ (x y : real), x ≤ y ∨ y ≤ x
real.le|real → real → Prop
real.lim_seq|real.cauchy_with_rate ?X ?M → pnat.pnat → ℚ
real.lim|real.cauchy_with_rate ?X ?M → real
real.lt|real → real → Prop
real.mul_comm|∀ (x y : real), x * y = y * x
real.mul_one|∀ (x : real), x * 1 = x
real.mul_pos|∀ (x y : real), 0 < x → 0 < y → 0 < x * y
real.mul|real → real → real
real.neg|real → real
real.of_int.inj|real.of_int ?a = real.of_int ?b → ?a = ?b
real.of_int|ℤ → real
real.of_nat_div|∀ (x y : ℕ), y ∣ x → real.of_nat (x / y) = real.of_nat x / real.of_nat y
real.of_nat|ℕ → real
real.of_num|num → real
real.of_rat_pow|∀ (a : ℚ) (n : ℕ), real.of_rat (a ^ n) = real.of_rat a ^ n
real.of_rat_zero|real.of_rat 0 = 0
real.of_rat|ℚ → real
real.one_mul|∀ (x : real), 1 * x = x
real.prio|num
real.re_abs|real → real
real.rep|real → rat_seq.reg_seq
real.right_distrib|∀ (x y z : real), (x + y) * z = x * z + y * z
real.sep|real → real → Prop
real.sub|real → real → real
real.ub|(real → Prop) → real → Prop
real.zero_add|∀ (x : real), 0 + x = x
real|Type₁
rec_on_app|∀ (H : ?P = ?P') (f : Π (x : ?A), ?P x) (a : ?A), eq.rec_on H f a == f a
rec_on_pull|∀ (H : ?P = ?P') (f : Π (x : ?A), ?P x) (a : ?A), eq.rec_on H f a = eq.rec_on (congr_fun H a) (f a)
reflexive|(?B → ?B → Prop) → Prop
relation.is_PER.mk|relation.symmetric ?R → relation.transitive ?R → relation.is_PER ?R
relation.is_equivalence.destruct|Π (n : relation.is_equivalence ?R), (Π (refl : relation.reflexive ?R) (symm : relation.symmetric ?R) (trans : relation.transitive ?R), ?C (relation.is_equivalence.mk refl symm trans)) → ?C n
relation.is_equivalence.mk|relation.reflexive ?R → relation.symmetric ?R → relation.transitive ?R → relation.is_equivalence ?R
relation.is_equivalence.rec|(Π (refl : relation.reflexive ?R) (symm : relation.symmetric ?R) (trans : relation.transitive ?R), ?C (relation.is_equivalence.mk refl symm trans)) → (Π (n : relation.is_equivalence ?R), ?C n)
relation.is_reflexive.mk|relation.reflexive ?R → relation.is_reflexive ?R
relation.is_symmetric.no_confusion|?v1 = ?v2 → relation.is_symmetric.no_confusion_type ?P ?v1 ?v2
relation.is_symmetric.rec_on|Π (n : relation.is_symmetric ?R), (Π (symm : relation.symmetric ?R), ?C (relation.is_symmetric.mk symm)) → ?C n
relation.is_symmetric.rec|(Π (symm : relation.symmetric ?R), ?C (relation.is_symmetric.mk symm)) → (Π (n : relation.is_symmetric ?R), ?C n)
relation.mp_like.destruct|Π (n : relation.mp_like ?R), (Π (app : Π {a : Type} {b : Type}, ?R a b → a → b), ?C (relation.mp_like.mk app)) → ?C n
relation.mp_like.induction_on|Π (n : relation.mp_like ?R), (Π (app : Π {a : Type} {b : Type}, ?R a b → a → b), ?C (relation.mp_like.mk app)) → ?C n
relation.mp_like.mk|(Π {a : Type} {b : Type}, ?R a b → a → b) → relation.mp_like ?R
relation.mp_like.no_confusion_type|Type → relation.mp_like ?R → relation.mp_like ?R → Type
relation.mp_like|(Type → Type → Type) → Type
relation.symmetric|(?T → ?T → Type) → Type
rfl|?a = ?a
right_cancel_semigroup.mk|Π (mul : ?A → ?A → ?A), (∀ (a b c : ?A), mul (mul a b) c = mul a (mul b c)) → (∀ (a b c : ?A), mul a b = mul c b → a = c) → right_cancel_semigroup ?A
ring.cases_on|Π (n : ring ?A), (Π (add : ?A → ?A → ?A) (add_assoc : ∀ (a b c : ?A), add (add a b) c = add a (add b c)) (zero : ?A) (zero_add : ∀ (a : ?A), add zero a = a) (add_zero : ∀ (a : ?A), add a zero = a) (neg : ?A → ?A) (add_left_inv : ∀ (a : ?A), add (neg a) a = zero) (add_comm : ∀ (a b : ?A), add a b = add b a) (mul : ?A → ?A → ?A) (mul_assoc : ∀ (a b c : ?A), mul (mul a b) c = mul a (mul b c)) (one : ?A) (one_mul : ∀ (a : ?A), mul one a = a) (mul_one : ∀ (a : ?A), mul a one = a) (left_distrib : ∀ (a b c : ?A), mul a (add b c) = add (mul a b) (mul a c)) (right_distrib : ∀ (a b c : ?A), mul (add a b) c = add (mul a c) (mul b c)), ?C (ring.mk add add_assoc zero zero_add add_zero neg add_left_inv add_comm mul mul_assoc one one_mul mul_one left_distrib right_distrib)) → ?C n
ring.destruct|Π (n : ring ?A), (Π (add : ?A → ?A → ?A) (add_assoc : ∀ (a b c : ?A), add (add a b) c = add a (add b c)) (zero : ?A) (zero_add : ∀ (a : ?A), add zero a = a) (add_zero : ∀ (a : ?A), add a zero = a) (neg : ?A → ?A) (add_left_inv : ∀ (a : ?A), add (neg a) a = zero) (add_comm : ∀ (a b : ?A), add a b = add b a) (mul : ?A → ?A → ?A) (mul_assoc : ∀ (a b c : ?A), mul (mul a b) c = mul a (mul b c)) (one : ?A) (one_mul : ∀ (a : ?A), mul one a = a) (mul_one : ∀ (a : ?A), mul a one = a) (left_distrib : ∀ (a b c : ?A), mul a (add b c) = add (mul a b) (mul a c)) (right_distrib : ∀ (a b c : ?A), mul (add a b) c = add (mul a c) (mul b c)), ?C (ring.mk add add_assoc zero zero_add add_zero neg add_left_inv add_comm mul mul_assoc one one_mul mul_one left_distrib right_distrib)) → ?C n
ring.mk|Π (add : ?A → ?A → ?A), (∀ (a b c : ?A), add (add a b) c = add a (add b c)) → (Π (zero : ?A), (∀ (a : ?A), add zero a = a) → (∀ (a : ?A), add a zero = a) → (Π (neg : ?A → ?A), (∀ (a : ?A), add (neg a) a = zero) → (∀ (a b : ?A), add a b = add b a) → (Π (mul : ?A → ?A → ?A), (∀ (a b c : ?A), mul (mul a b) c = mul a (mul b c)) → (Π (one : ?A), (∀ (a : ?A), mul one a = a) → (∀ (a : ?A), mul a one = a) → (∀ (a b c : ?A), mul a (add b c) = add (mul a b) (mul a c)) → (∀ (a b c : ?A), mul (add a b) c = add (mul a c) (mul b c)) → ring ?A))))
ring.no_confusion_type|Type → ring ?A → ring ?A → Type
ring.rec_on|Π (n : ring ?A), (Π (add : ?A → ?A → ?A) (add_assoc : ∀ (a b c : ?A), add (add a b) c = add a (add b c)) (zero : ?A) (zero_add : ∀ (a : ?A), add zero a = a) (add_zero : ∀ (a : ?A), add a zero = a) (neg : ?A → ?A) (add_left_inv : ∀ (a : ?A), add (neg a) a = zero) (add_comm : ∀ (a b : ?A), add a b = add b a) (mul : ?A → ?A → ?A) (mul_assoc : ∀ (a b c : ?A), mul (mul a b) c = mul a (mul b c)) (one : ?A) (one_mul : ∀ (a : ?A), mul one a = a) (mul_one : ∀ (a : ?A), mul a one = a) (left_distrib : ∀ (a b c : ?A), mul a (add b c) = add (mul a b) (mul a c)) (right_distrib : ∀ (a b c : ?A), mul (add a b) c = add (mul a c) (mul b c)), ?C (ring.mk add add_assoc zero zero_add add_zero neg add_left_inv add_comm mul mul_assoc one one_mul mul_one left_distrib right_distrib)) → ?C n
ring.rec|(Π (add : ?A → ?A → ?A) (add_assoc : ∀ (a b c : ?A), add (add a b) c = add a (add b c)) (zero : ?A) (zero_add : ∀ (a : ?A), add zero a = a) (add_zero : ∀ (a : ?A), add a zero = a) (neg : ?A → ?A) (add_left_inv : ∀ (a : ?A), add (neg a) a = zero) (add_comm : ∀ (a b : ?A), add a b = add b a) (mul : ?A → ?A → ?A) (mul_assoc : ∀ (a b c : ?A), mul (mul a b) c = mul a (mul b c)) (one : ?A) (one_mul : ∀ (a : ?A), mul one a = a) (mul_one : ∀ (a : ?A), mul a one = a) (left_distrib : ∀ (a b c : ?A), mul a (add b c) = add (mul a b) (mul a c)) (right_distrib : ∀ (a b c : ?A), mul (add a b) c = add (mul a c) (mul b c)), ?C (ring.mk add add_assoc zero zero_add add_zero neg add_left_inv add_comm mul mul_assoc one one_mul mul_one left_distrib right_distrib)) → (Π (n : ring ?A), ?C n)
ring.zero_mul|∀ (a : ?A), 0 * a = 0
ring|Type → Type
semigroup.mk|Π (mul : ?A → ?A → ?A), (∀ (a b c : ?A), mul (mul a b) c = mul a (mul b c)) → semigroup ?A
semigroup|Type → Type
semiring._trans_of_to_mul_zero_class|Π (A : Type) [s : semiring A], has_zero A
semiring.mk|Π (add : ?A → ?A → ?A), (∀ (a b c : ?A), add (add a b) c = add a (add b c)) → (Π (zero : ?A), (∀ (a : ?A), add zero a = a) → (∀ (a : ?A), add a zero = a) → (∀ (a b : ?A), add a b = add b a) → (Π (mul : ?A → ?A → ?A), (∀ (a b c : ?A), mul (mul a b) c = mul a (mul b c)) → (Π (one : ?A), (∀ (a : ?A), mul one a = a) → (∀ (a : ?A), mul a one = a) → (∀ (a b c : ?A), mul a (add b c) = add (mul a b) (mul a c)) → (∀ (a b c : ?A), mul (add a b) c = add (mul a c) (mul b c)) → (∀ (a : ?A), mul zero a = zero) → (∀ (a : ?A), mul a zero = zero) → semiring ?A)))
semiring.to_mul_zero_class|Π (A : Type) [s : semiring A], mul_zero_class A
semiring_has_pow_nat|has_pow_nat ?A
semiring|Type → Type
set.Inter_eq_comp_Union_comp|∀ (s : ?I → set ?X), set.Inter s = set.compl (set.Union (λ (i : ?I), set.compl (s i)))
set.Inter|(?I → set ?X) → set ?X
set.Prod_eq_of_bij_on|∀ (f : ?C → ?B) {g : ?A → ?C}, set.bij_on g ?s ?t → set.Prod ?t f = set.Prod ?s (λ (i : ?A), f (g i))
set.Prod_semigroup.Prod_semigroup_empty|∀ (dflt : ?B) (f : ?A → ?B), set.Prod_semigroup.Prod_semigroup dflt set.empty f = dflt
set.Prod|set ?A → (?A → ?B) → ?B
set.Sum_eq_of_bij_on|∀ (f : ?C → ?B) {g : ?A → ?C}, set.bij_on g ?s ?t → set.Sum ?t f = set.Sum ?s (λ (i : ?A), f (g i))
set.Sum|set ?A → (?A → ?B) → ?B
set.Union|(?I → set ?X) → set ?X
set.bInter|set ?I → (?I → set ?X) → set ?X
set.bUnion_union|∀ (s t : set ?X) (f : ?X → set ?Y), set.bUnion (set.union s t) f = set.union (set.bUnion s f) (set.bUnion t f)
set.bUnion|set ?I → (?I → set ?X) → set ?X
set.bij_on.mk|set.maps_to ?f ?a ?b → set.inj_on ?f ?a → set.surj_on ?f ?a ?b → set.bij_on ?f ?a ?b
set.bij_on_of_inv_on|set.maps_to ?f ?a ?b → set.maps_to ?g ?b ?a → set.inv_on ?g ?f ?a ?b → set.bij_on ?f ?a ?b
set.bij_on|(?X → ?Y) → set ?X → set ?Y → Prop
set.bijective_iff_bij_on_univ|function.bijective ?f ↔ set.bij_on ?f set.univ set.univ
set.bounded_exists_congr|(∀ ⦃x : ?A⦄, set.mem x ?S → (?P x ↔ ?Q x)) → (∃ ⦃x : ?A⦄, set.mem x ?S ∧ ?P x) = ∃ ⦃x : ?A⦄, set.mem x ?S ∧ ?Q x
set.bounded_forall_empty_iff|(Π ⦃x : ?X⦄, set.mem x set.empty → ?P x) ↔ true
set.card_image_eq_of_inj_on|set.inj_on ?f ?s → set.card (set.image ?f ?s) = set.card ?s
set.card_le_of_inj_on|∀ (a : set ?A) (b : set ?B) [_inst_1 : set.finite b], (∃ (f : ?A → ?B), set.inj_on f a ∧ set.subset (set.image f a) b) → set.card a ≤ set.card b
set.card_union_of_disjoint|set.inter ?s₁ ?s₂ = set.empty → set.card (set.union ?s₁ ?s₂) = set.card ?s₁ + set.card ?s₂
set.card|set ?A → ℕ
set.compl|set ?X → set ?X
set.diff_eq|∀ (s t : set ?X), set.diff s t = set.inter s (set.compl t)
set.diff|set ?X → set ?X → set ?X
set.disjoint_sets_union|set.disjoint_sets ?s → set.disjoint_sets ?t → (∀ (x y : set ?X), set.mem x ?s ∧ set.mem y ?t → set.inter x y = set.empty) → set.disjoint_sets (set.union ?s ?t)
set.disjoint_sets|set (set ?X) → Prop
set.empty_inter|∀ (a : set ?X), set.inter set.empty a = set.empty
set.empty_ne_univ|set.empty ≠ set.univ
set.empty_subset|∀ (s : set ?X), set.subset set.empty s
set.empty|set ?X
set.eq_on|(?X → ?Y) → (?X → ?Y) → set ?X → Prop
set.eq_univ_of_univ_subset|set.subset set.univ ?s → ?s = set.univ
set.exists_two_of_card_gt_one|1 < set.card ?s → (∃ (a b : ?A), set.mem a ?s ∧ set.mem b ?s ∧ a ≠ b)
set.ext|(∀ (x : ?X), set.mem x ?a ↔ set.mem x ?b) → ?a = ?b
set.filter.eventually_Sup_iff|∀ (P : ?A → Prop) (S : set (set.filter ?A)), set.filter.eventually P (⨆ S) ↔ ∀ ⦃x : set.filter ?A⦄, set.mem x S → set.filter.eventually P x
set.filter.eventually_Sup|(∀ ⦃x : set.filter ?A⦄, set.mem x ?S → set.filter.eventually ?P x) → set.filter.eventually ?P (⨆ ?S)
set.filter.eventually_iff_mpr|set.filter.eventually (λ (x : ?A), ?P x ↔ ?Q x) ?F → set.filter.eventually ?Q ?F → set.filter.eventually ?P ?F
set.filter.eventually_mono|set.filter.eventually ?P ?F → (Π (x : ?A), ?P x → ?Q x) → set.filter.eventually ?Q ?F
set.filter.eventually_of_eventually_sup_right|set.filter.eventually ?P (?F₁ ⊔ ?F₂) → set.filter.eventually ?P ?F₂
set.filter.exists_of_frequently|set.filter.frequently ?P ?F → Exists ?P
set.filter.frequently_mp|set.filter.eventually (λ (x : ?A), ?P x → ?Q x) ?F → set.filter.frequently ?P ?F → set.filter.frequently ?Q ?F
set.filter.not_frequently_of_eventually|set.filter.eventually (λ (x : ?A), ¬?P x) ?F → ¬set.filter.frequently ?P ?F
set.filter.subset_of_principal_le_principal|set.filter.principal ?s ≤ set.filter.principal ?t → set.subset ?s ?t
set.filter|Type → Type
set.finite_iff_finite_of_bij_on|set.bij_on ?f ?s ?t → (set.finite ?s ↔ set.finite ?t)
set.finite_of_bij_on'|set.bij_on ?f ?s ?t → set.finite ?s
set.finite_of_inj_on|set.maps_to ?f ?s ?t → set.inj_on ?f ?s → set.finite ?s
set.finite_of_surj_on|set.surj_on ?f ?s ?t → set.finite ?t
set.finite_powerset|∀ (s : set ?A) [_inst_1 : set.finite s], set.finite (set.powerset s)
set.finite|set ?A → Prop
set.image|(?X → ?Y) → set ?X → set ?Y
set.inj_on_empty|∀ (f : ?X → ?Y), set.inj_on f set.empty
set.inj_on_of_bij_on|set.bij_on ?f ?a ?b → set.inj_on ?f ?a
set.inj_on_of_card_image_eq|set.card (set.image ?f ?s) = set.card ?s → set.inj_on ?f ?s
set.inj_on_of_eq_on|(∀ ⦃x : ?X⦄, set.mem x ?a → ?f1 x = ?f2 x) → set.inj_on ?f1 ?a → set.inj_on ?f2 ?a
set.inj_on_of_inj_on_of_subset|set.inj_on ?f ?b → set.subset ?a ?b → set.inj_on ?f ?a
set.inj_on|(?X → ?Y) → set ?X → Prop
set.injective_iff_inj_on_univ|function.injective ?f ↔ set.inj_on ?f set.univ
set.insert|?X → set ?X → set ?X
set.inter_sUnion_nonempty_of_inter_nonempty|set.mem ?t ?S → set.inter ?s ?t ≠ set.empty → set.inter ?s (set.sUnion ?S) ≠ set.empty
set.inter_univ|∀ (a : set ?X), set.inter a set.univ = a
set.inter|set ?X → set ?X → set ?X
set.inv_on|(?Y → ?X) → (?X → ?Y) → set ?X → set ?Y → Prop
set.left_inv_on_inv_fun_of_inj_on|∀ (dflt : ?X), set.inj_on ?f ?a → set.left_inv_on (set.inv_fun ?f ?a dflt) ?f ?a
set.left_inv_on_of_surj_on_right_inv_on|set.surj_on ?f ?a ?b → set.right_inv_on ?f ?g ?a → set.left_inv_on ?f ?g ?b
set.map.bijective_of_equiv|set.map.equiv ?f1 ?f2 → set.map.bijective ?f1 → set.map.bijective ?f2
set.map.bijective|set.map ?a ?b → Prop
set.map.image_eq_of_bijective|set.map.bijective ?f → set.image (set.map.func ?f) ?a = ?b
set.map.image_eq_of_surjective|set.map.surjective ?f → set.image (set.map.func ?f) ?a = ?b
set.map.injective_of_left_inverse|set.map.left_inverse ?g ?f → set.map.injective ?f
set.map.left_inverse_comp|set.map.left_inverse ?f' ?f → set.map.left_inverse ?g' ?g → set.map.left_inverse (set.map.comp ?f' ?g') (set.map.comp ?g ?f)
set.map.left_inverse_of_surjective_of_right_inverse|set.map.surjective ?f → set.map.right_inverse ?f ?g → set.map.left_inverse ?f ?g
set.map.mk|Π (func : ?X → ?Y), set.maps_to func ?a ?b → set.map ?a ?b
set.map.no_confusion_type|Type → set.map ?a ?b → set.map ?a ?b → Type
set.map.surjective_comp|set.map.surjective ?g → set.map.surjective ?f → set.map.surjective (set.map.comp ?g ?f)
set.map.surjective_of_equiv|set.map.equiv ?f1 ?f2 → set.map.surjective ?f1 → set.map.surjective ?f2
set.map.surjective_of_right_inverse|set.map.right_inverse ?g ?f → set.map.surjective ?f
set.maps_to_inv_fun|set.mem ?dflt ?a → set.maps_to (set.inv_fun ?f ?a ?dflt) ?b ?a
set.maps_to_of_bij_on|set.bij_on ?f ?a ?b → set.maps_to ?f ?a ?b
set.map|set ?X → set ?Y → Type
set.mem_image_compl|∀ (t : set ?X) (S : set (set ?X)), set.mem t (set.image set.compl S) ↔ set.mem (set.compl t) S
set.mem_powerset_iff|∀ (x s : set ?X), set.mem x (set.powerset s) ↔ set.subset x s
set.mem|?X → set ?X → Prop
set.not_mem_empty|∀ (x : ?X), ¬set.mem x set.empty
set.right_inv_on_of_inj_on_of_left_inv_on|set.maps_to ?f ?a ?b → set.maps_to ?g ?b ?a → set.inj_on ?f ?a → set.left_inv_on ?f ?g ?b → set.right_inv_on ?f ?g ?a
set.sInter|set (set ?X) → set ?X
set.sUnion_inter_nonempty_of_inter_nonempty|set.mem ?t ?S → set.inter ?t ?s ≠ set.empty → set.inter (set.sUnion ?S) ?s ≠ set.empty
set.sUnion|set (set ?X) → set ?X
set.sep|(?X → Prop) → set ?X → set ?X
set.set_of|(?X → Prop) → set ?X
set.subset|set ?X → set ?X → Prop
set.surj_on_inv_fun_of_inj_on|∀ (dflt : ?X), set.maps_to ?f ?a ?b → set.inj_on ?f ?a → set.surj_on (set.inv_fun ?f ?a dflt) ?b ?a
set.surj_on_of_eq_on|(∀ ⦃x : ?X⦄, set.mem x ?a → ?f1 x = ?f2 x) → set.surj_on ?f1 ?a ?b → set.surj_on ?f2 ?a ?b
set.surjective_iff_surj_on_univ|function.surjective ?f ↔ set.surj_on ?f set.univ set.univ
set.to_finset_eq_empty_of_eq_empty|?s = set.empty → set.to_finset ?s = finset.empty
set.union|set ?X → set ?X → set ?X
set.univ|set ?X
setoid.mk|Π (r : ?A → ?A → Prop), equivalence r → setoid ?A
setoid.rec|(Π (r : ?A → ?A → Prop) (iseqv : equivalence r), ?C (setoid.mk r iseqv)) → (Π (n : setoid ?A), ?C n)
setoid.refl|∀ (a : ?A), setoid.r a a
setoid|Type → Type
set|Type → Type
sigma.dtrip_eq|∀ (H₁ : ?a₁ = ?a₂) (H₂ : eq.rec_on H₁ ?b₁ = ?b₂), cast (dcongr_arg2 ?C H₁ H₂) ?c₁ = ?c₂ → ⟨?a₁, ?b₁, ?c₁⟩ = ⟨?a₂, ?b₂, ?c₂⟩
sigma.eq|∀ (H₁ : sigma.pr1 ?p₁ = sigma.pr1 ?p₂), eq.rec_on H₁ (sigma.pr2 ?p₁) = sigma.pr2 ?p₂ → ?p₁ = ?p₂
sigma.eta|∀ (s : sigma ?B), ⟨sigma.pr1 s, sigma.pr2 s⟩ = s
sigma.heq|?B == ?B' → sigma.pr1 ?p == sigma.pr1 ?p' → sigma.pr2 ?p == sigma.pr2 ?p' → ?p == ?p'
sigma.is_inhabited|inhabited (sigma ?B)
sigma.lex.accessible|acc ?Ra ?a → (∀ (a : ?A), well_founded (?Rb a)) → (∀ (b : ?B ?a), acc (sigma.lex ?Ra ?Rb) ⟨?a, b⟩)
sigma.lex.cases_on|sigma.lex ?Ra ?Rb ?a ?a → (Π {a₁ : ?A} {b₁ : ?B a₁} (a₂ : ?A) (b₂ : ?B a₂), ?Ra a₁ a₂ → ?C ⟨a₁, b₁⟩ ⟨a₂, b₂⟩) → (Π (a : ?A) {b₁ b₂ : ?B a}, ?Rb a b₁ b₂ → ?C ⟨a, b₁⟩ ⟨a, b₂⟩) → ?C ?a ?a
sigma.lex.wf|well_founded ?Ra → (∀ (x : ?A), well_founded (?Rb x)) → well_founded (sigma.lex ?Ra ?Rb)
sigma.lex|(?A → ?A → Prop) → (Π (a : ?A), ?B a → ?B a → Prop) → sigma ?B → sigma ?B → Prop
sigma.mk|Π (pr1 : ?A), ?B pr1 → sigma ?B
sigma.pr1'|sigma ?B → ?A
sigma.pr1.mk|∀ (pr1 : ?A) (pr2 : ?B pr1), sigma.pr1 ⟨pr1, pr2⟩ = pr1
sigma.pr2'|Π (x : Σ (a : ?A), sigma (?C a)), ?B (sigma.pr1 x)
sigma.pr3'|Π (x : Σ (a : ?A) (b : ?B a), sigma (?D a b)), ?C (sigma.pr1 x) (sigma.pr1 (sigma.pr2 x))
sigma.pr3|Π (x : Σ (a : ?A), sigma (?C a)), ?C (sigma.pr1 x) (sigma.pr1 (sigma.pr2 x))
sigma.pr4|Π (x : Σ (a : ?A) (b : ?B a), sigma (?D a b)), ?D (sigma.pr1 x) (sigma.pr1 (sigma.pr2 x)) (sigma.pr1 (sigma.pr2 (sigma.pr2 x)))
sigma.rec|(Π (pr1 : ?A) (pr2 : ?B pr1), ?C ⟨pr1, pr2⟩) → (Π (n : sigma ?B), ?C n)
sigma|(?A → Type) → Type
sign_mul|∀ (a b : ?A), sign (a * b) = sign a * sign b
sign_neg|∀ (a : ?A), sign (-a) = -sign a
sign_of_pos|?a > 0 → sign ?a = 1
sign_one|sign 1 = 1
sign_sign|∀ (a : ?A), sign (sign a) = sign a
sign_zero|sign 0 = 0
sign|?A → ?A
size_of|?A → ℕ
std.priority.max|num
stream.all|(?A → Prop) → stream ?A → Prop
stream.any|(?A → Prop) → stream ?A → Prop
stream.cycle_eq|∀ (l : list ?A) (h : l ≠ list.nil), stream.cycle l h = stream.append l (stream.cycle l h)
stream.drop|ℕ → stream ?A → stream ?A
stream.eta|∀ (s : stream ?A), stream.cons (stream.head s) (stream.tail s) = s
stream.even_tail|∀ (s : stream ?A), stream.even (stream.tail s) = stream.odd s
stream.ext|(∀ (n : ℕ), stream.nth n ?s₁ = stream.nth n ?s₂) → ?s₁ = ?s₂
stream.interleave_eq|∀ (s₁ s₂ : stream ?A), stream.interleave s₁ s₂ = stream.cons (stream.head s₁) (stream.cons (stream.head s₂) (stream.interleave (stream.tail s₁) (stream.tail s₂)))
stream.interleave|stream ?A → stream ?A → stream ?A
stream.lex|(?A → ?A → Prop) → stream ?A → stream ?A → Prop
stream.map|(?A → ?B) → stream ?A → stream ?B
stream.mem_interleave_left|∀ (s₂ : stream ?A), stream.mem ?a ?s₁ → stream.mem ?a (stream.interleave ?s₁ s₂)
stream.mem|?A → stream ?A → Prop
stream.nth|ℕ → stream ?A → ?A
stream.odd|stream ?A → stream ?A
stream.tail_zip|∀ (f : ?A → ?B → ?C) (s₁ : stream ?A) (s₂ : stream ?B), stream.tail (stream.zip f s₁ s₂) = stream.zip f (stream.tail s₁) (stream.tail s₂)
stream.tail|stream ?A → stream ?A
stream.take_lemma|∀ (s₁ s₂ : stream ?A), (∀ (n : ℕ), stream.approx n s₁ = stream.approx n s₂) → s₁ = s₂
stream.unfolds_eq|∀ (g : ?A → ?B) (f : ?A → ?A) (a : ?A), stream.unfolds g f a = stream.cons (g a) (stream.unfolds g f (f a))
stream.zip_eq|∀ (f : ?A → ?B → ?C) (s₁ : stream ?A) (s₂ : stream ?B), stream.zip f s₁ s₂ = stream.cons (f (stream.head s₁) (stream.head s₂)) (stream.zip f (stream.tail s₁) (stream.tail s₂))
stream.zip|(?A → ?B → ?C) → stream ?A → stream ?B → stream ?C
stream|Type → Type
strict_order.mk|Π (lt : ?A → ?A → Prop), (∀ (a : ?A), ¬lt a a) → (∀ (a b c : ?A), lt a b → lt b c → lt a c) → strict_order ?A
strictly_decreasing_neg_of_strictly_increasing|strictly_increasing ?f → strictly_decreasing (λ (x : ?B), -?f x)
strictly_decreasing_of_left_inverse|function.left_inverse ?g ?f → strictly_decreasing ?g → strictly_decreasing ?f
strictly_decreasing_of_strictly_decreasing_comp_left|function.left_inverse ?f ?h → strictly_increasing ?h → strictly_decreasing (function.comp ?g ?f) → strictly_decreasing ?g
strictly_decreasing_of_strictly_increasing_neg'|strictly_increasing (λ (x : ?A), ?f (-x)) → strictly_decreasing ?f
strictly_increasing_of_left_inverse|function.left_inverse ?g ?f → strictly_increasing ?g → strictly_increasing ?f
strictly_increasing_of_strictly_decreasing_comp_left|function.left_inverse ?f ?h → strictly_decreasing ?h → strictly_decreasing (function.comp ?g ?f) → strictly_increasing ?g
strictly_increasing_of_strictly_decreasing_neg|strictly_decreasing (λ (x : ?B), -?f x) → strictly_increasing ?f
strictly_increasing_of_strictly_increasing_comp_right|function.left_inverse ?h ?g → strictly_increasing ?h → strictly_increasing (function.comp ?g ?f) → strictly_increasing ?f
string.empty|string
string.rec|?C string.empty → (Π (a : char) (a_1 : string), ?C a_1 → ?C (string.str a a_1)) → (Π (n : string), ?C n)
string.str|char → string → string
string|Type₁
strong_order_pair._trans_of_to_order_pair|has_lt ?A
strong_order_pair.mk|Π (le : ?A → ?A → Prop), (∀ (a : ?A), le a a) → (∀ (a b c : ?A), le a b → le b c → le a c) → (∀ (a b : ?A), le a b → le b a → a = b) → (Π (lt : ?A → ?A → Prop), (∀ (a b : ?A), le a b ↔ lt a b ∨ a = b) → (∀ (a : ?A), ¬lt a a) → strong_order_pair ?A)
sub_le_sub|?a ≤ ?b → ?c ≤ ?d → ?a - ?d ≤ ?b - ?c
sub_lt_sub|?a < ?b → ?c < ?d → ?a - ?d < ?b - ?c
sub_nmul|∀ (a : ?A), ?m ≥ ?n → (?m - ?n)⬝a = ?m⬝a + -(?n⬝a)
sub_self|∀ (a : ?A), a - a = 0
sub_sub|∀ (a b c : ?A), a - b - c = a - (b + c)
sub_zero|∀ (a : ?A), a - 0 = a
subsingleton.helim|?A = ?B → (∀ (a : ?A) (b : ?B), a == b)
subtype.eq|subtype.elt_of ?a1 = subtype.elt_of ?a2 → ?a1 = ?a2
subtype.has_decidable_eq|Π (s₁ s₂ : subtype ?P), decidable (s₁ = s₂)
subtype.is_inhabited|?P ?a → inhabited (subtype ?P)
subtype.no_confusion_type|Type → subtype ?P → subtype ?P → Type
subtype.rec|(Π (elt_of : ?A) (has_property : ?P elt_of), ?C (subtype.tag elt_of has_property)) → (Π (n : subtype ?P), ?C n)
subtype.tag|Π (elt_of : ?A), ?P elt_of → subtype ?P
subtype|(?A → Prop) → Type
sub|?A → ?A → ?A
succ_nmul'|∀ (n : ℕ) (a : ?A), nat.succ n⬝a = n⬝a + a
succ_nmul|∀ (n : ℕ) (a : ?A), nat.succ n⬝a = a + n⬝a
sum.inl_inj|sum.intro_left ?B ?a₁ = sum.intro_left ?B ?a₂ → ?a₁ = ?a₂
sum.inl_ne_inr|∀ (a : ?A) (b : ?B), sum.inl a ≠ sum.inr b
sum.inl|?A → ?A ⊎ ?B
sum.inr_inj|sum.intro_right ?A ?b₁ = sum.intro_right ?A ?b₂ → ?b₁ = ?b₂
sum.inr|?B → ?A ⊎ ?B
sum.rec_on|Π (n : ?A ⊎ ?B), (Π (a : ?A), ?C (sum.inl a)) → (Π (a : ?B), ?C (sum.inr a)) → ?C n
sum.rec|(Π (a : ?A), ?C (sum.inl a)) → (Π (a : ?B), ?C (sum.inr a)) → (Π (n : ?A ⊎ ?B), ?C n)
sum|Type → Type → Type
sup.assoc|∀ (a b c : ?A), a ⊔ b ⊔ c = a ⊔ (b ⊔ c)
sup.comm|∀ (a b : ?A), a ⊔ b = b ⊔ a
sup_le|?a ≤ ?c → ?b ≤ ?c → ?a ⊔ ?b ≤ ?c
sup_self|∀ (a : ?A), a ⊔ a = a
sup|?A → ?A → ?A
symmetric|(?B → ?B → Prop) → Prop
tactic.and_then|tactic → tactic → tactic
tactic.apply|tactic.expr → tactic
tactic.at_most|tactic → num → tactic
tactic.beta|tactic
tactic.blast|tactic.opt_identifier_list → tactic.opt_identifier_list → tactic
tactic.builtin|tactic
tactic.cases_on|Π (n : tactic), ?C tactic.builtin → ?C n
tactic.cases|tactic.expr → tactic.opt_identifier_list → tactic
tactic.change|tactic.expr → tactic
tactic.check_expr|tactic.expr → tactic
tactic.clears|tactic.identifier_list → tactic
tactic.clear|tactic.identifier_list → tactic
tactic.determ|tactic → tactic
tactic.discard|tactic → num → tactic
tactic.do|num → tactic → tactic
tactic.eapply|tactic.expr → tactic
tactic.exact|tactic.expr → tactic
tactic.exfalso|tactic
tactic.existsi|tactic.expr → tactic
tactic.expr.cases_on|Π (n : tactic.expr), ?C tactic.expr.builtin → ?C n
tactic.expr.induction_on|Π (n : tactic.expr), ?C tactic.expr.builtin → ?C n
tactic.expr.rec_on|Π (n : tactic.expr), ?C tactic.expr.builtin → ?C n
tactic.expr.rec|?C tactic.expr.builtin → (Π (n : tactic.expr), ?C n)
tactic.expr_list.induction_on|Π (n : tactic.expr_list), ?C tactic.expr_list.nil → (Π (a : tactic.expr) (a_1 : tactic.expr_list), ?C a_1 → ?C (tactic.expr_list.cons a a_1)) → ?C n
tactic.expr_list.no_confusion|?v1 = ?v2 → tactic.expr_list.no_confusion_type ?P ?v1 ?v2
tactic.expr|Type₁
tactic.fail|tactic
tactic.fapply|tactic.expr → tactic
tactic.fixpoint|(tactic → tactic) → tactic
tactic.focus_at|tactic → num → tactic
tactic.focus|tactic → tactic
tactic.grind|tactic
tactic.id|tactic
tactic.info|tactic
tactic.intros|tactic.opt_identifier_list → tactic
tactic.intro|tactic.opt_identifier_list → tactic
tactic.krewrite_tac|tactic.expr_list → tactic
tactic.left|tactic
tactic.location|Type₁
tactic.no_confusion_type|Type → tactic → tactic → Type
tactic.none_expr|tactic.expr
tactic.norm_num|tactic
tactic.note_tac|tactic.identifier → tactic.expr → tactic
tactic.now|tactic
tactic.or_else|tactic → tactic → tactic
tactic.par|tactic → tactic → tactic
tactic.rec_on|Π (n : tactic), ?C tactic.builtin → ?C n
tactic.rec_simp|tactic
tactic.rec|?C tactic.builtin → (Π (n : tactic), ?C n)
tactic.refine|tactic.expr → tactic
tactic.rename|tactic.identifier → tactic.identifier → tactic
tactic.repeat1|tactic → tactic
tactic.repeat|tactic → tactic
tactic.replace|tactic.expr → tactic.with_expr → tactic.location → tactic
tactic.reverts|tactic.identifier_list → tactic
tactic.revert|tactic.identifier_list → tactic
tactic.rexact|tactic.expr → tactic
tactic.right|tactic
tactic.rotate|num → tactic
tactic.simp|tactic
tactic.split|tactic
tactic.state|tactic
tactic.subst|tactic.identifier_list → tactic
tactic.symmetry|tactic
tactic.trace|string → tactic
tactic.trivial|tactic
tactic.try_for|tactic → num → tactic
tactic.try|tactic → tactic
tactic.whnf|tactic
tactic|Type₁
tc.accessible|acc ?R ?z → acc (tc ?R) ?z
tc.base|Π (a b : ?A), ?R a b → tc ?R a b
tc.cases_on|tc ?R ?a ?a → (Π (a b : ?A), ?R a b → ?C a b) → (Π (a b c : ?A), tc ?R a b → tc ?R b c → ?C a c) → ?C ?a ?a
tc.rec_on|tc ?R ?a ?a → (Π (a b : ?A), ?R a b → ?C a b) → (Π (a b c : ?A), tc ?R a b → tc ?R b c → ?C a b → ?C b c → ?C a c) → ?C ?a ?a
tc.rec|(Π (a b : ?A), ?R a b → ?C a b) → (Π (a b c : ?A), tc ?R a b → tc ?R b c → ?C a b → ?C b c → ?C a c) → (Π {a a_1 : ?A}, tc ?R a a_1 → ?C a a_1)
tc.trans|∀ (a b c : ?A), tc ?R a b → tc ?R b c → tc ?R a c
tc.wf|well_founded ?R → well_founded (tc ?R)
tc|(?A → ?A → Prop) → ?A → ?A → Prop
the_spec|Π (H : exists_unique ?p), ?p (the H)
the|exists_unique ?p → ?A
tneg.elim|~?A → ?A → empty
tneg.empty|~empty
tneg.intro|(?A → empty) → ~?A
tneg.tabsurd|?A → ~?A → ?B
tneg.tmt|(?A → ?B) → ~?B → ~?A
tneg.tneg|Type → Type
to_nodup_list|list ?A → nodup_list ?A
top|?A
total|(?B → ?B → Prop) → Prop
trans_rel_left|∀ (R : ?A → ?A → Prop), R ?a ?b → ?b = ?c → R ?a ?c
trans_rel_right|∀ (R : ?A → ?A → Prop), ?a = ?b → R ?b ?c → R ?a ?c
transitive|(?B → ?B → Prop) → Prop
trivial|true
true.cases_on|true → ?C → ?C
true.intro|true
true.rec_on|true → ?C → ?C
true.rec|?C → true → ?C
true_and|∀ (a : Prop), true ∧ a ↔ a
true_iff_false|true ↔ false ↔ false
true_iff|∀ (a : Prop), true ↔ a ↔ a
true_imp|∀ (a : Prop), true → a ↔ a
true_ne_false|¬true = false
true_or|∀ (a : Prop), true ∨ a ↔ true
true|Prop
two_ge_one|2 ≥ 1
two_gt_one|2 > 1
two_ne_zero|2 ≠ 0
two_pos|1 + 1 > 0
type_eq_of_heq|?a == ?b → ?A = ?B
unique_of_exists_unique|exists_unique ?p → (Π {y₁ y₂ : ?A}, ?p y₁ → ?p y₂ → y₁ = y₂)
unit.cases_on|Π (n : unit), ?C unit.star → ?C n
unit.eq_star|∀ (a : unit), a = unit.star
unit.eq|∀ (a b : unit), a = b
unit.has_decidable_eq|decidable_eq unit
unit.induction_on|Π (n : unit), ?C unit.star → ?C n
unit.is_inhabited|inhabited unit
unit.measurable|measurable unit
unit.rec_on|Π (n : unit), ?C unit.star → ?C n
unit.rec|?C unit.star → (Π (n : unit), ?C n)
unit.star|unit
unit.subsingleton|subsingleton unit
unit|Type₁
weak_order.cases_on|Π (n : weak_order ?A), (Π (le : ?A → ?A → Prop) (le_refl : ∀ (a : ?A), le a a) (le_trans : ∀ (a b c : ?A), le a b → le b c → le a c) (le_antisymm : ∀ (a b : ?A), le a b → le b a → a = b), ?C (weak_order.mk le le_refl le_trans le_antisymm)) → ?C n
weak_order.destruct|Π (n : weak_order ?A), (Π (le : ?A → ?A → Prop) (le_refl : ∀ (a : ?A), le a a) (le_trans : ∀ (a b c : ?A), le a b → le b c → le a c) (le_antisymm : ∀ (a b : ?A), le a b → le b a → a = b), ?C (weak_order.mk le le_refl le_trans le_antisymm)) → ?C n
weak_order.induction_on|Π (n : weak_order ?A), (Π (le : ?A → ?A → Prop) (le_refl : ∀ (a : ?A), le a a) (le_trans : ∀ (a b c : ?A), le a b → le b c → le a c) (le_antisymm : ∀ (a b : ?A), le a b → le b a → a = b), ?C (weak_order.mk le le_refl le_trans le_antisymm)) → ?C n
weak_order.mk|Π (le : ?A → ?A → Prop), (∀ (a : ?A), le a a) → (∀ (a b c : ?A), le a b → le b c → le a c) → (∀ (a b : ?A), le a b → le b a → a = b) → weak_order ?A
weak_order.no_confusion_type|Type → weak_order ?A → weak_order ?A → Type
weak_order.no_confusion|?v1 = ?v2 → weak_order.no_confusion_type ?P ?v1 ?v2
weak_order.rec_on|Π (n : weak_order ?A), (Π (le : ?A → ?A → Prop) (le_refl : ∀ (a : ?A), le a a) (le_trans : ∀ (a b c : ?A), le a b → le b c → le a c) (le_antisymm : ∀ (a b : ?A), le a b → le b a → a = b), ?C (weak_order.mk le le_refl le_trans le_antisymm)) → ?C n
weak_order.rec|(Π (le : ?A → ?A → Prop) (le_refl : ∀ (a : ?A), le a a) (le_trans : ∀ (a b c : ?A), le a b → le b c → le a c) (le_antisymm : ∀ (a b : ?A), le a b → le b a → a = b), ?C (weak_order.mk le le_refl le_trans le_antisymm)) → (Π (n : weak_order ?A), ?C n)
weak_order.to_has_le|Π (A : Type) [s : weak_order A], has_le A
weak_order_Prop|weak_order Prop
weak_order_dual|weak_order ?A → weak_order ?A
weak_order_fun|Π (A : Type) (B : Type) [_inst_1 : weak_order B], weak_order (A → B)
weak_order|Type → Type
well_founded.apply|well_founded ?R → (∀ (a : ?A), acc ?R a)
well_founded.cases_on|well_founded ?R → ((∀ (a : ?A), acc ?R a) → ?C) → ?C
well_founded.fix_F_eq|∀ (F : Π (x : ?A), (Π (y : ?A), ?R y x → ?C y) → ?C x) (x : ?A) (r : acc ?R x), well_founded.fix_F F x r = F x (λ (y : ?A) (p : ?R y x), well_founded.fix_F F y (acc.inv r p))
well_founded.fix_F|(Π (x : ?A), (Π (y : ?A), ?R y x → ?C y) → ?C x) → (Π (x : ?A), acc ?R x → ?C x)
well_founded.fix_eq|∀ (F : Π (x : ?A), (Π (y : ?A), ?R y x → ?C y) → ?C x) (x : ?A), well_founded.fix F x = F x (λ (y : ?A) (h : ?R y x), well_founded.fix F y)
well_founded.fix|(Π (x : ?A), (Π (y : ?A), ?R y x → ?C y) → ?C x) → (Π (x : ?A), ?C x)
well_founded.induction_on|well_founded ?R → ((∀ (a : ?A), acc ?R a) → ?C) → ?C
well_founded.induction|Π (a : ?A), (Π (x : ?A), (Π (y : ?A), ?R y x → ?C y) → ?C x) → ?C a
well_founded.intro_k|well_founded ?R → ℕ → well_founded ?R
well_founded.intro|(∀ (a : ?A), acc ?R a) → well_founded ?R
well_founded.rec_on|well_founded ?R → ((∀ (a : ?A), acc ?R a) → ?C) → ?C
well_founded.recursion|Π (a : ?A), (Π (x : ?A), (Π (y : ?A), ?R y x → ?C y) → ?C x) → ?C a
well_founded.rec|((∀ (a : ?A), acc ?R a) → ?C) → well_founded ?R → ?C
well_founded|(?A → ?A → Prop) → Prop
wf.ind_on|Π (x : ?A), (Π (x : ?A), (Π (y : ?A), wf_strict_order.lt y x → ?P y) → ?P x) → ?P x
wf.rec_on|Π (x : ?A), (Π (x : ?A), (Π (y : ?A), wf_strict_order.lt y x → ?P y) → ?P x) → ?P x
wf_strict_order._trans_of_to_strict_order|Π (A : Type) [s : wf_strict_order A], has_lt A
wf_strict_order.cases_on|Π (n : wf_strict_order ?A), (Π (lt : ?A → ?A → Prop) (lt_irrefl : ∀ (a : ?A), ¬lt a a) (lt_trans : ∀ (a b c : ?A), lt a b → lt b c → lt a c) (wf_rec : Π (P : ?A → Type), (Π (x : ?A), (Π (y : ?A), lt y x → P y) → P x) → (Π (x : ?A), P x)), ?C (wf_strict_order.mk lt lt_irrefl lt_trans wf_rec)) → ?C n
wf_strict_order.destruct|Π (n : wf_strict_order ?A), (Π (lt : ?A → ?A → Prop) (lt_irrefl : ∀ (a : ?A), ¬lt a a) (lt_trans : ∀ (a b c : ?A), lt a b → lt b c → lt a c) (wf_rec : Π (P : ?A → Type), (Π (x : ?A), (Π (y : ?A), lt y x → P y) → P x) → (Π (x : ?A), P x)), ?C (wf_strict_order.mk lt lt_irrefl lt_trans wf_rec)) → ?C n
wf_strict_order.induction_on|Π (n : wf_strict_order ?A), (Π (lt : ?A → ?A → Prop) (lt_irrefl : ∀ (a : ?A), ¬lt a a) (lt_trans : ∀ (a b c : ?A), lt a b → lt b c → lt a c) (wf_rec : Π (P : ?A → Type), (Π (x : ?A), (Π (y : ?A), lt y x → P y) → P x) → (Π (x : ?A), P x)), ?C (wf_strict_order.mk lt lt_irrefl lt_trans wf_rec)) → ?C n
wf_strict_order.mk|Π (lt : ?A → ?A → Prop), (∀ (a : ?A), ¬lt a a) → (∀ (a b c : ?A), lt a b → lt b c → lt a c) → (Π (P : ?A → Type), (Π (x : ?A), (Π (y : ?A), lt y x → P y) → P x) → (Π (x : ?A), P x)) → wf_strict_order ?A
wf_strict_order.no_confusion_type|Type → wf_strict_order ?A → wf_strict_order ?A → Type
wf_strict_order.no_confusion|?v1 = ?v2 → wf_strict_order.no_confusion_type ?P ?v1 ?v2
wf_strict_order.rec_on|Π (n : wf_strict_order ?A), (Π (lt : ?A → ?A → Prop) (lt_irrefl : ∀ (a : ?A), ¬lt a a) (lt_trans : ∀ (a b c : ?A), lt a b → lt b c → lt a c) (wf_rec : Π (P : ?A → Type), (Π (x : ?A), (Π (y : ?A), lt y x → P y) → P x) → (Π (x : ?A), P x)), ?C (wf_strict_order.mk lt lt_irrefl lt_trans wf_rec)) → ?C n
wf_strict_order.rec|(Π (lt : ?A → ?A → Prop) (lt_irrefl : ∀ (a : ?A), ¬lt a a) (lt_trans : ∀ (a b c : ?A), lt a b → lt b c → lt a c) (wf_rec : Π (P : ?A → Type), (Π (x : ?A), (Π (y : ?A), lt y x → P y) → P x) → (Π (x : ?A), P x)), ?C (wf_strict_order.mk lt lt_irrefl lt_trans wf_rec)) → (Π (n : wf_strict_order ?A), ?C n)
wf_strict_order.to_strict_order|Π (A : Type) [s : wf_strict_order A], strict_order A
wf_strict_order|Type → Type
zero_add|∀ (a : ?A), 0 + a = a
zero_div|∀ (a : ?A), 0 / a = 0
zero_gt_neg_one|-1 < 0
zero_le_one|0 ≤ 1
zero_lt_one|0 < 1
zero_mul|∀ (a : ?A), 0 * a = 0
zero_ne_one_class.cases_on|Π (n : zero_ne_one_class ?A), (Π (zero one : ?A) (zero_ne_one : zero ≠ one), ?C (zero_ne_one_class.mk zero one zero_ne_one)) → ?C n
zero_ne_one_class.destruct|Π (n : zero_ne_one_class ?A), (Π (zero one : ?A) (zero_ne_one : zero ≠ one), ?C (zero_ne_one_class.mk zero one zero_ne_one)) → ?C n
zero_ne_one_class.induction_on|Π (n : zero_ne_one_class ?A), (Π (zero one : ?A) (zero_ne_one : zero ≠ one), ?C (zero_ne_one_class.mk zero one zero_ne_one)) → ?C n
zero_ne_one_class.mk|Π (zero one : ?A), zero ≠ one → zero_ne_one_class ?A
zero_ne_one_class.no_confusion_type|Type → zero_ne_one_class ?A → zero_ne_one_class ?A → Type
zero_ne_one_class.no_confusion|?v1 = ?v2 → zero_ne_one_class.no_confusion_type ?P ?v1 ?v2
zero_ne_one_class.rec_on|Π (n : zero_ne_one_class ?A), (Π (zero one : ?A) (zero_ne_one : zero ≠ one), ?C (zero_ne_one_class.mk zero one zero_ne_one)) → ?C n
zero_ne_one_class.rec|(Π (zero one : ?A) (zero_ne_one : zero ≠ one), ?C (zero_ne_one_class.mk zero one zero_ne_one)) → (Π (n : zero_ne_one_class ?A), ?C n)
zero_ne_one_class.to_has_one|Π (A : Type) [s : zero_ne_one_class A], has_one A
zero_ne_one_class.to_has_zero|Π (A : Type) [s : zero_ne_one_class A], has_zero A
zero_ne_one_class|Type → Type
zero_ne_one|0 ≠ 1
zero_nmul|∀ (a : ?A), 0⬝a = 0
zero_pow|?m > 0 → 0 ^ ?m = 0
zero_sub|∀ (a : ?A), 0 - a = -a
zero|?A
]
