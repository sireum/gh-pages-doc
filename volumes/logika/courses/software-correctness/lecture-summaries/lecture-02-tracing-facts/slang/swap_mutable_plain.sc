// #Sireum #Logika
import org.sireum._

val m: Z = randomInt()
val n: Z = randomInt()
var x: Z = m
var y: Z = n
x = x + y
y = x - y
x = x - y
assert(x == n & y == m)
