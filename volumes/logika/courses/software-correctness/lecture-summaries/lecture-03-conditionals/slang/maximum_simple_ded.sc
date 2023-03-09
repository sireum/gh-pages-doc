// #Sireum #Logika
import org.sireum._
val x: Z = randomInt()
val y: Z = randomInt()

var z: Z = 0
if (x < y) {
  Deduce(|- (x < y))
  Deduce(|- (x <= y))
  z = y
  Deduce(|- (x <= z))
  Deduce(|- (z == y))
} else {
  Deduce(|- (!(x < y)))
  Deduce(|- (y <= x))
  z = x
  Deduce(|- (y <= z))
  Deduce(|- (z == x))
}
assert(z == x | z == y)
assert(y <= z & x <= z)