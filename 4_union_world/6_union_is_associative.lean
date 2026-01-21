ext x
apply Iff.intro
intro h
rcases h with ha|hb
rcases ha  with ha1 | ha2
left
exact ha1
right
left
exact ha2
right
right
exact hb
intro h
rcases h with h1|h2
left
left
exact h1
rcases h2 with h21|h22
left
right
exact h21
right
exact h22
