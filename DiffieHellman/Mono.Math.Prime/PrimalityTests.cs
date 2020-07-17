namespace DiffieHellman.Mono.Math.Prime
{
    using System;
    using System.Security.Cryptography;
    using Math;

    [CLSCompliant(false)]
	internal sealed class PrimalityTests
	{
		private static int GetSPPRounds(BigInteger bi, ConfidenceFactor confidence)
		{
			int num = bi.bitCount();
			int num2 = (num <= 100) ? 27 : ((num <= 150) ? 18 : ((num <= 200) ? 15 : ((num <= 250) ? 12 : ((num <= 300) ? 9 : ((num <= 350) ? 8 : ((num <= 400) ? 7 : ((num <= 500) ? 6 : ((num <= 600) ? 5 : ((num <= 800) ? 4 : ((num > 1250) ? 2 : 3))))))))));
			switch (confidence)
			{
			case ConfidenceFactor.ExtraLow:
				num2 >>= 2;
				if (num2 == 0)
				{
					return 1;
				}
				return num2;
			case ConfidenceFactor.Low:
				num2 >>= 1;
				if (num2 == 0)
				{
					return 1;
				}
				return num2;
			case ConfidenceFactor.Medium:
				return num2;
			case ConfidenceFactor.High:
				return num2 <<= 1;
			case ConfidenceFactor.ExtraHigh:
				return num2 <<= 2;
			case ConfidenceFactor.Provable:
				throw new Exception("The Rabin-Miller test can not be executed in a way such that its results are provable");
			default:
				throw new ArgumentOutOfRangeException("confidence");
			}
		}

		public static bool RabinMillerTest(BigInteger bi, ConfidenceFactor confidence)
		{
			int sPPRounds = GetSPPRounds(bi, confidence);
			BigInteger bigInteger = bi - 1;
			int num = bigInteger.LowestSetBit();
			BigInteger exp = bigInteger >> num;
			int bits = bi.bitCount();
			BigInteger bigInteger2 = null;
			RandomNumberGenerator rng = RandomNumberGenerator.Create();
			BigInteger.ModulusRing modulusRing = new BigInteger.ModulusRing(bi);
			for (int i = 0; i < sPPRounds; i++)
			{
				do
				{
					bigInteger2 = BigInteger.genRandom(bits, rng);
				}
				while (!(bigInteger2 > 1) || !(bigInteger2 < bi));
				if (bigInteger2.gcd(bi) != 1u)
				{
					return false;
				}
				BigInteger bigInteger3 = modulusRing.Pow(bigInteger2, exp);
				if (bigInteger3 == 1u)
				{
					continue;
				}
				bool flag = false;
				for (int j = 0; j < num; j++)
				{
					if (bigInteger3 == bigInteger)
					{
						flag = true;
						break;
					}
					bigInteger3 = bigInteger3 * bigInteger3 % bi;
				}
				if (!flag)
				{
					return false;
				}
			}
			return true;
		}

		public static bool SmallPrimeSppTest(BigInteger bi, ConfidenceFactor confidence)
		{
			int sPPRounds = GetSPPRounds(bi, confidence);
			BigInteger bigInteger = bi - 1;
			int num = bigInteger.LowestSetBit();
			BigInteger exp = bigInteger >> num;
			BigInteger.ModulusRing modulusRing = new BigInteger.ModulusRing(bi);
			for (int i = 0; i < sPPRounds; i++)
			{
				BigInteger bigInteger2 = modulusRing.Pow(BigInteger.smallPrimes[i], exp);
				if (bigInteger2 == 1u)
				{
					continue;
				}
				bool flag = false;
				for (int j = 0; j < num; j++)
				{
					if (bigInteger2 == bigInteger)
					{
						flag = true;
						break;
					}
					bigInteger2 = bigInteger2 * bigInteger2 % bi;
				}
				if (!flag)
				{
					return false;
				}
			}
			return true;
		}
	}
}
