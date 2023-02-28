# Program Specification Based Programming

This is lesson 004 of a "Program Specification Based Programming" course.

All comments are welcome at luc.duponcheel[at]gmail.com.

## Introduction

In lesson 003 we have defined some `trait Program` members in terms of `trait Computation` members.

In this lesson we define some `trait Program` members in terms of function level `trait Product` members, some in
terms of `trait Computation` members and some in terms of both `trait Computation` members and function level
`trait Product` members.

Below the, yet to be defined, declared `trait` members so far are briefly repeated.

```scala
private[psbp] trait Function[>-->[-_, +_], &&[+_, +_]]:

  // external declared

  def functionFromTuple2Lift[Z, Y, X]: (Tuple2[Z, Y] => X) => ((Z && Y) >--> X)

  def functionFromTuple3Lift[Z, Y, X, W]: (Tuple3[Z, Y, X] => W) => ((Z && Y && X) >--> W)

  // ...  
```

and

```scala
private[psbp] trait IfThenElse[
    >-->[-_, +_]: [>-->[-_, +_]] =>> LocalDefinition[>-->, &&],
    &&[+_, +_]
]:

  // internal declared

  extension [Z, Y](`z>-t->y`: => Z >--> Y)
    private[psbp] def Or(`z>-f->y`: => Z >--> Y): (Z && Boolean) >--> Y
```

and

```scala
private[psbp] trait Product[>-->[-_, +_], &&[+_, +_]]:

  // external declared

  def `(z&&y)>-->z`[Z, Y]: (Z && Y) >--> Z

  def `(z&&y)>-->y`[Z, Y]: (Z && Y) >--> Y

  extension [Z, Y, X](`z>-->y`: Z >--> Y) def &&(`z>-->x`: => Z >--> X): Z >--> (Y && X)
```

## Content

The members above all involve `&&`.

### Function level Data Structures

Below the product related data structure function concepts are specified.

```scala
private[psbp] trait Product[&&[+_, +_]]:

  // internal declared

  private[psbp] def `(z&&y)=>z`[Z, Y]: (Z && Y) => Z

  private[psbp] def `(z&&y)=>y`[Z, Y]: (Z && Y) => Y

  private[psbp] def unfoldProduct[Z, Y, X]: (Z => Y) => (Z => X) => (Z => (Y && X))
```

### Implementing `Function` in terms of `Computation` and function level `Product`

```scala
package psbp.implementation.function

import psbp.specification.dataStructure.{Product}

import psbp.specification.computation.{Computation}

private[psbp] trait Function[
    C[+_]: Computation: [C[+_]] =>> Product[[Z, Y] =>> Z => C[Y], &&],
    &&[+_, +_]: psbp.specification.Product
] extends psbp.specification.function.Function[[Z, Y] =>> Z => C[Y], &&]:

  private type >--> = [Z, Y] =>> Z => C[Y]

  private lazy val summonedComputation = summon[Computation[C]]

  import summonedComputation.{expressionLift}

  private lazy val summonedProduct = summon[Product[[Z, Y] =>> Z => C[Y], &&]]

  import summonedProduct.{
    `(z&&y)>-->z` => `(z&&y)=>c[z]`,
    `(z&&y)>-->y` => `(z&&y)=>c[y]`
  }

  private lazy val summonedFunctionLevelProduct = summon[psbp.specification.Product[&&]]

  import summonedFunctionLevelProduct.{unfoldProduct}

  // external defined

  override def functionLift[Z, Y]: (Z => Y) => (Z >--> Y) = `z=>y` =>
    z => expressionLift(`z=>y`(z))

  override def functionFromTuple2Lift[Z, Y, X]
      : (Tuple2[Z, Y] => X) => ((Z && Y) => C[X]) =
    `tuple2[z,y]=>x` =>
      `z&&y` =>
        `(z&&y)=>c[z]`(`z&&y`) >= { z =>
          `(z&&y)=>c[y]`(`z&&y`) >= { y =>
            expressionLift(`tuple2[z,y]=>x`((z, y)))
          }
        }

  override def functionFromTuple3Lift[Z, Y, X, W]
      : (Tuple3[Z, Y, X] => W) => ((Z && Y && X) => C[W]) =
    `tuple3[z,y,x]=>w` =>
      `z&&y&&x` =>
        `(z&&y&&x)=>c[z]`(`z&&y&&x`) >= { z =>
          `(z&&y&&x)=>c[y]`(`z&&y&&x`) >= { y =>
            `(z&&y&&x)=>c[x]`(`z&&y&&x`) >= { x =>
              expressionLift(`tuple3[z,y,x]=>w`((z, y, x)))
            }
          }
        }        
```

### Updating `Product`

Recall that for technical reasons we always define extension members in terms of declared method members.

Therefore we declare an extra internal method member `product` in `Product`.

```scala
package psbp.specification.dataStructure

import psbp.specification.algorithm.{SequentialComposition}

private[psbp] trait Product[>-->[-_, +_]: SequentialComposition, &&[+_, +_]]:

  // external declared

  def `(z&&y)>-->z`[Z, Y]: (Z && Y) >--> Z

  def `(z&&y)>-->y`[Z, Y]: (Z && Y) >--> Y

  // external defined

  extension [Z, Y, X](`z>-->y`: Z >--> Y)
    def &&(`z>-->x`: => Z >--> X): Z >--> (Y && X) = product(`z>-->y`, `z>-->x`)  

  extension [Z, Y, X, W](`z>-->x`: Z >--> X)
    def &&&(`y>-->w`: => Y >--> W): (Z && Y) >--> (X && W) =
      (`(z&&y)>-->z` >--> `z>-->x`) && (`(z&&y)>-->y` >--> `y>-->w`)

  def `(z&&y&&x)>-->z`[Z, Y, X]: (Z && Y && X) >--> Z =
    `(z&&y)>-->z` >--> `(z&&y)>-->z`

  def `(z&&y&&x)>-->y`[Z, Y, X]: (Z && Y && X) >--> Y =
    `(z&&y)>-->z` >--> `(z&&y)>-->y`

  def `(z&&y&&x)>-->x`[Z, Y, X]: (Z && Y && X) >--> X =
    `(z&&y)>-->y`

  def `(z&&y&&x)>-->(y&&x)`[Z, Y, X]: (Z && Y && X) >--> (Y && X) =
    `(z&&y&&x)>-->y` && `(z&&y)>-->y`

  def `(z&&y&&x)>-->(z&&x)`[Z, Y, X]: (Z && Y && X) >--> (Z && X) =
    `(z&&y&&x)>-->z` && `(z&&y)>-->y`

  def `(z&&y&&x)>-->(z&&y)`[Z, Y, X]: (Z && Y && X) >--> (Z && Y) =
    `(z&&y&&x)>-->z` && `(z&&y&&x)>-->y`

  // ...

  // internal declared

  private[psbp] def product[Z, Y, X](
      `z>-->y`: Z >--> Y,
      `z>-->x`: => Z >--> X
  ): Z >--> (Y && X)
```

### Partially implementing `Product` in terms of function level `Product`

```scala
package psbp.specification.dataStructure

import psbp.specification.function.{Function}

import psbp.specification.algorithm.{SequentialComposition}

private[psbp] trait Product[
    >-->[-_, +_]: SequentialComposition: [>-->[-_, +_]] =>> Function[>-->, &&],
    &&[+_, +_]: psbp.specification.Product
]:

  private lazy val summonedFunction = summon[Function[>-->, &&]]

  import summonedFunction.{functionLift}

  private lazy val summonedProduct = summon[psbp.specification.Product[&&]]

  import summonedProduct.{`(z&&y)=>z`, `(z&&y)=>y`}

  // external defined

  def `(z&&y)>-->z`[Z, Y]: (Z && Y) >--> Z = functionLift(`(z&&y)=>z`)

  def `(z&&y)>-->y`[Z, Y]: (Z && Y) >--> Y = functionLift(`(z&&y)=>y`)

  extension [Z, Y, X](`z>-->y`: Z >--> Y)
    def &&(`z>-->x`: => Z >--> X): Z >--> (Y && X) = product(`z>-->y`, `z>-->x`)

  extension [Z, Y, X, W](`z>-->x`: Z >--> X)
    def &&&(`y>-->w`: => Y >--> W): (Z && Y) >--> (X && W) =
      (`(z&&y)>-->z` >--> `z>-->x`) && (`(z&&y)>-->y` >--> `y>-->w`)

  def `(z&&y&&x)>-->z`[Z, Y, X]: (Z && Y && X) >--> Z =
    `(z&&y)>-->z` >--> `(z&&y)>-->z`

  def `(z&&y&&x)>-->y`[Z, Y, X]: (Z && Y && X) >--> Y =
    `(z&&y)>-->z` >--> `(z&&y)>-->y`

  def `(z&&y&&x)>-->x`[Z, Y, X]: (Z && Y && X) >--> X =
    `(z&&y)>-->y`

  def `(z&&y&&x)>-->(y&&x)`[Z, Y, X]: (Z && Y && X) >--> (Y && X) =
    `(z&&y&&x)>-->y` && `(z&&y)>-->y`

  def `(z&&y&&x)>-->(z&&x)`[Z, Y, X]: (Z && Y && X) >--> (Z && X) =
    `(z&&y&&x)>-->z` && `(z&&y)>-->y`

  def `(z&&y&&x)>-->(z&&y)`[Z, Y, X]: (Z && Y && X) >--> (Z && Y) =
    `(z&&y&&x)>-->z` && `(z&&y&&x)>-->y`

  // ...

  // internal declared

  private[psbp] def product[Z, Y, X](
      `z>-->y`: Z >--> Y,
      `z>-->x`: => Z >--> X
  ): Z >--> (Y && X)
```

We also added extension member `&&&`.

### Implementing `Product` in terms of `Computation` and function level `Product`

```scala
package psbp.implementation.dataStructure

import psbp.specification.function.{Function}

import psbp.specification.algorithm.{SequentialComposition}

import psbp.specification.computation.{Computation}

private[psbp] trait Product[
    C[+_]: Computation
         : [C[+_]] =>> SequentialComposition[[Z, Y] =>> Z => C[Y]]
         : [C[+_]] =>> Function[[Z, Y] =>> Z => C[Y], &&], 
    &&[+_, +_]: psbp.specification.Product]
    extends psbp.specification.dataStructure.Product[[Z, Y] =>> Z => C[Y], &&]:

  private lazy val summonedComputation = summon[Computation[C]]

  import summonedComputation.{expressionLift}

  private lazy val summonedProduct = summon[psbp.specification.Product[&&]]

  import summonedProduct.{unfoldProduct}

  // external defined

  private[psbp] override def product[Z, Y, X](
      `z=>c[y]`: Z => C[Y],
      `z=>c[x]`: => Z => C[X]
  ): Z => C[Y && X] =
    z =>
      `z=>c[y]`(z) >= { y =>
        `z=>c[x]`(z) >= { x =>
          expressionLift(unfoldProduct(_ => y)(_ => x)(()))
        }
      }
```

## Conclusion

We have defined almost all `trait Program` members in terms of `trait Computation` members and function level
`trait Product` members.













