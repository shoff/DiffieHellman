namespace DiffieHellman.Mono.Math.Prime
{
    using System;
    using Math;

    [CLSCompliant(false)]
	internal delegate bool PrimalityTest(BigInteger bi, ConfidenceFactor confidence);
}
