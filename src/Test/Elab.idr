module Test.Elab

import Language.Reflection
import Language.Reflection.Syntax
import Language.Reflection.Types
import Decidable.Equality

%language ElabReflection

public export
foo : (decEq : (x1 : a) -> (x2 : a) -> Dec (x1 = x2)) -> DecEq a
foo = %runElab do
  name <- singleCon (UN $ Basic "DecEq")
  check (var name)
