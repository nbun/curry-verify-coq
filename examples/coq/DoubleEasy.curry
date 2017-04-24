module DoubleEasy(double,even) where

import Nat
import Test.Prop

double x = add x x

even Z         = True
even (S Z)     = False
even (S (S n)) = even n

evendouble x = always (even (double x))

