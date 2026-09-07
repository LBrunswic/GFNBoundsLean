---
id: 0001
title: Every proof touching `pstar` is a three-case split on `St`
kind: pattern
tags: [st, pstar, case-analysis]
confidence: established
sources: [GFNBounds/Doubling/Setting.lean:256]
created: 2026-09-07
---
## When

The goal mentions `pstar S cap f x` for a universally quantified `x : St`, or you need to prove
something at every state.

## Do

```lean
rcases x with (_ | j) | _
· -- x = .src, i.e. `.lad 0`: `pstar_src` fires, `pstar S cap f .src = f .sink`
· -- x = .lad (j + 1): `by_cases h : HasDouble cap (j + 1)` then `simp only [pstar_lad_succ, h]`
· -- x = .sink: `pstar_sink`, a `Finset.sum` over `Finset.Icc 1 S.d`
```

The middle case almost always continues

```lean
by_cases h : HasDouble cap (j + 1)
· simp only [pstar_lad_succ, h, if_true]
· simp only [pstar_lad_succ, h, if_false]
```

## Why

`St` is `lad : ℕ → St | sink`, and `St.src` is a `@[match_pattern] abbrev` for `.lad 0`, so `.lad`
splits again on zero-versus-successor. The three arms of `rcases` line up exactly with the three
defining equations of `pstar`, which is why it was written as a total closed-form match rather
than as `∑' y, kern x y * f y`: there is no integrability side condition to discharge, only cases.

`pstar_add`, `pstar_smul`, `pstar_nonneg`, `pstar_bounded` and `pstar_const` in `Setting.lean` are
all this same skeleton — read one before writing a new one.
