import Lean.LabelAttribute

/--
We'd like to import this from Batteries, but it's not in Batteries.
At's in the testsuite for batteries, upon which we shouldn't depend for our tests.
As such, we define it again here.
-/
register_label_attr dummy_label_attr
