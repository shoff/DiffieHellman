namespace DiffieHellman.Mono.Math.Prime.Generator
{
    using System;
    using Math;

    [CLSCompliant(false)]
	internal class SequentialSearchPrimeGeneratorBase : PrimeGeneratorBase
	{
		protected virtual BigInteger GenerateSearchBase(int bits, object Context)
		{
			BigInteger bigInteger = BigInteger.genRandom(bits);
			bigInteger.setBit(0u);
			return bigInteger;
		}

		public override BigInteger GenerateNewPrime(int bits)
		{
			return GenerateNewPrime(bits, null);
		}

		public virtual BigInteger GenerateNewPrime(int bits, object Context)
		{
			BigInteger bigInteger = GenerateSearchBase(bits, Context);
			uint num = bigInteger % 3234846615u;
			int trialDivisionBounds = this.TrialDivisionBounds;
			uint[] smallPrimes = BigInteger.smallPrimes;
			_ = this.PrimalityTest;
			while (true)
			{
				if (num % 3u != 0 && num % 5u != 0 && num % 7u != 0 && num % 11u != 0 && num % 13u != 0 && num % 17u != 0 && num % 19u != 0 && num % 23u != 0 && num % 29u != 0)
				{
					int num2 = 9;
					while (true)
					{
						if (num2 < smallPrimes.Length && smallPrimes[num2] <= trialDivisionBounds)
						{
							if (bigInteger % smallPrimes[num2] == 0)
							{
								break;
							}
							num2++;
							continue;
						}
						if (!IsPrimeAcceptable(bigInteger, Context) || !this.PrimalityTest(bigInteger, this.Confidence))
						{
							break;
						}
						return bigInteger;
					}
				}
				num += 2;
				if (num >= 3234846615u)
				{
					num = (uint)((int)num - -1060120681);
				}
				bigInteger.Incr2();
			}
		}

		protected virtual bool IsPrimeAcceptable(BigInteger bi, object Context)
		{
			return true;
		}
	}
}
