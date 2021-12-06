package utils

class FreshNameGenerator {
  private val ix = new java.util.concurrent.atomic.AtomicLong()
  def generateFreshName(): String =
    s"_${ix.getAndIncrement()}"
}
