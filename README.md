[![CI](https://github.com/cdsmith/cfrac/actions/workflows/ci.yml/badge.svg)](https://github.com/cdsmith/cfrac/actions/workflows/ci.yml)

This is the code that goes along with my blog post at
https://cdsmithus.medium.com/continued-fractions-haskell-equational-reasoning-property-testing-and-rewrite-rules-in-action-77a16d750e3f

There are some small revisions since the blog post.  Contributions are appreciated.

This is not yet released to Hackage.  If someone is interested in depending on
it, please ask and I'll revise and release it.  But it was intended as just
playing around, so I don't yet see value in publishing and taking up Hackage
namespace and resources.

There are several previous Hackage packages related to continued fractions:

* https://hackage.haskell.org/package/cf looks similar to this one and claims to
  offer even more operations, including portions of the Floating class.
  However, I wasn't able to get it to work.  Most operations just hang.
* https://hackage.haskell.org/package/continued-fraction implements only a
  couple operations, such as conversion to and from rationals, and convergents.
  In particular, it does not define a new type, nor offer any classes in the Num
  hierarchy.
* https://hackage.haskell.org/package/continued-fractions also implements only a
  few operations, though there are several variations on them.  Again, there are
  no standard arithmetic classes or operations.
