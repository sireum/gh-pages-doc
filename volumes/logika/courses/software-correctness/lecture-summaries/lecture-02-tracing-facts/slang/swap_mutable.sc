// #Sireum #Logika
import org.sireum._

val m: Z = randomInt()
val n: Z = randomInt()
var x: Z = m
var y: Z = n
x = x + y
Deduce(|- (At(x, 0) == m))
Deduce(|- (y == n))
Deduce(|- (x == At(x, 0) + y))
Deduce(|- (x == m + n))
y = x - y
Deduce(|- (x == m + n))
Deduce(|- (At(y, 0) == n))
Deduce(|- (y == x - At(y, 0)))
Deduce(|- (y == m))
x = x - y
Deduce(|- (At(x, 1) == m + n))
Deduce(|- (y == m))
Deduce(|- (x == At(x, 1) - y))
assert(x == n & y == m)
