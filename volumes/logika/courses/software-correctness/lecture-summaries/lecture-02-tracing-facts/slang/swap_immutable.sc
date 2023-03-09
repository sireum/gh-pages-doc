// #Sireum #Logika
import org.sireum._

val m: Z = randomInt()
val n: Z = randomInt()
val z: Z = m + n
Deduce(|- (z == m + n))
val y: Z = z - n
Deduce(|- (z == m + n))
Deduce(|- (y == m))
val x: Z = z - y
Deduce(|- (z == m + n))
Deduce(|- (y == m))
Deduce(|- (x == n))
assert(x == n & y == m)
