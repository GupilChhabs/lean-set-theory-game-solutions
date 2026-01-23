ext x
apply Iff.intro
intro h
rcases h with h1|h2
constructor
left
exact h1
left
exact h1
constructor
right
exact h2.left
right
exact h2.right
intro h
rw [inter_distrib_left] at h
rcases h with ha|hb
left
exact ha.right
rcases hb with hb1|hb2
left
exact hb1
right
constructor
exact hb2
exact right
