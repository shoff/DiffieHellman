namespace DiffieHellman.Mono.Math
{
    using System;
    using System.Security.Cryptography;
    using Prime;
    using Prime.Generator;

	internal class BigInteger
	{
		public enum Sign
		{
			Negative = -1,
			Zero,
			Positive
		}

		public sealed class ModulusRing
		{
			private readonly BigInteger mod;

			private readonly BigInteger constant;

			public ModulusRing(BigInteger mod)
			{
				this.mod = mod;
				uint num = mod.length << 1;
                this.constant = new BigInteger(Sign.Positive, num + 1)
                {
                    data = {[num] = 1u}
                };
                this.constant /= mod;
			}

			public void BarrettReduction(BigInteger x)
			{
				BigInteger bigInteger = this.mod;
				uint length = bigInteger.length;
				uint num = length + 1;
				uint num2 = length - 1;
				if (x.length >= length)
				{
					if (x.data.Length < x.length)
					{
						throw new IndexOutOfRangeException("x out of range");
					}
					BigInteger bigInteger2 = new BigInteger(Sign.Positive, x.length - num2 + this.constant.length);
					Kernel.Multiply(x.data, num2, x.length - num2, this.constant.data, 0u, this.constant.length, bigInteger2.data, 0u);
					uint num3 = x.length = ((x.length > num) ? num : x.length);
					x.Normalize();
					BigInteger bigInteger3 = new BigInteger(Sign.Positive, num);
					Kernel.MultiplyMod2p32pmod(bigInteger2.data, (int)num, (int)(bigInteger2.length - num), bigInteger.data, 0, (int)bigInteger.length, bigInteger3.data, 0, (int)num);
					bigInteger3.Normalize();
					if (bigInteger3 < x)
					{
						Kernel.MinusEq(x, bigInteger3);
					}
					else
					{
						BigInteger bigInteger4 = new BigInteger(Sign.Positive, num + 1);
						bigInteger4.data[num] = 1u;
						Kernel.MinusEq(bigInteger4, bigInteger3);
						Kernel.PlusEq(x, bigInteger4);
					}
					while (x >= bigInteger)
					{
						Kernel.MinusEq(x, bigInteger);
					}
				}
			}

			public BigInteger Multiply(BigInteger a, BigInteger b)
			{
				if (a == 0u || b == 0u)
				{
					return 0;
				}
				if (a.length >= this.mod.length << 1)
				{
					a %= this.mod;
				}
				if (b.length >= this.mod.length << 1)
				{
					b %= this.mod;
				}
				if (a.length >= this.mod.length)
				{
					BarrettReduction(a);
				}
				if (b.length >= this.mod.length)
				{
					BarrettReduction(b);
				}
				BigInteger bigInteger = new BigInteger(a * b);
				BarrettReduction(bigInteger);
				return bigInteger;
			}

			public BigInteger Difference(BigInteger a, BigInteger b)
			{
				Sign sign = Kernel.Compare(a, b);
				BigInteger bigInteger;
				switch (sign)
				{
				case Sign.Zero:
					return 0;
				case Sign.Positive:
					bigInteger = a - b;
					break;
				case Sign.Negative:
					bigInteger = b - a;
					break;
				default:
					throw new Exception();
				}
				if (bigInteger >= this.mod)
				{
					if (bigInteger.length >= this.mod.length << 1)
					{
						bigInteger %= this.mod;
					}
					else
					{
						BarrettReduction(bigInteger);
					}
				}
				if (sign == Sign.Negative)
				{
					bigInteger = this.mod - bigInteger;
				}
				return bigInteger;
			}

			public BigInteger Pow(BigInteger b, BigInteger exp)
			{
				if ((this.mod.data[0] & 1) == 1)
				{
					return OddPow(b, exp);
				}
				return EvenPow(b, exp);
			}

			public BigInteger EvenPow(BigInteger b, BigInteger exp)
			{
				BigInteger bigInteger = new BigInteger(1, this.mod.length << 1);
				BigInteger bigInteger2 = new BigInteger(b % this.mod, this.mod.length << 1);
				uint num = (uint)exp.bitCount();
				uint[] wkSpace = new uint[this.mod.length << 1];
				for (uint num2 = 0u; num2 < num; num2++)
				{
					if (exp.testBit(num2))
					{
						Array.Clear(wkSpace, 0, wkSpace.Length);
						Kernel.Multiply(bigInteger.data, 0u, bigInteger.length, bigInteger2.data, 0u, bigInteger2.length, wkSpace, 0u);
						bigInteger.length += bigInteger2.length;
						uint[] data = wkSpace;
						wkSpace = bigInteger.data;
						bigInteger.data = data;
						BarrettReduction(bigInteger);
					}
					Kernel.SquarePositive(bigInteger2, ref wkSpace);
					BarrettReduction(bigInteger2);
					if (bigInteger2 == 1u)
					{
						return bigInteger;
					}
				}
				return bigInteger;
			}

			private BigInteger OddPow(BigInteger b, BigInteger exp)
			{
				BigInteger bigInteger = new BigInteger(Montgomery.ToMont(1, this.mod), this.mod.length << 1);
				BigInteger bigInteger2 = new BigInteger(Montgomery.ToMont(b, this.mod), this.mod.length << 1);
				uint mPrime = Montgomery.Inverse(this.mod.data[0]);
				uint num = (uint)exp.bitCount();
				uint[] wkSpace = new uint[this.mod.length << 1];
				for (uint num2 = 0u; num2 < num; num2++)
				{
					if (exp.testBit(num2))
					{
						Array.Clear(wkSpace, 0, wkSpace.Length);
						Kernel.Multiply(bigInteger.data, 0u, bigInteger.length, bigInteger2.data, 0u, bigInteger2.length, wkSpace, 0u);
						bigInteger.length += bigInteger2.length;
						uint[] data = wkSpace;
						wkSpace = bigInteger.data;
						bigInteger.data = data;
						Montgomery.Reduce(bigInteger, this.mod, mPrime);
					}
					Kernel.SquarePositive(bigInteger2, ref wkSpace);
					Montgomery.Reduce(bigInteger2, this.mod, mPrime);
				}
				Montgomery.Reduce(bigInteger, this.mod, mPrime);
				return bigInteger;
			}

			public BigInteger Pow(uint b, BigInteger exp)
			{
				if (b != 2)
				{
					if ((this.mod.data[0] & 1) == 1)
					{
						return OddPow(b, exp);
					}
					return EvenPow(b, exp);
				}
				if ((this.mod.data[0] & 1) == 1)
				{
					return OddModTwoPow(exp);
				}
				return EvenModTwoPow(exp);
			}

			private unsafe BigInteger OddPow(uint b, BigInteger exp)
			{
				exp.Normalize();
				uint[] wkSpace = new uint[this.mod.length << 2];
				BigInteger bi = Montgomery.ToMont(b, this.mod);
				bi = new BigInteger(bi, this.mod.length << 2);
				uint mPrime = Montgomery.Inverse(this.mod.data[0]);
				uint bitNum = (uint)(exp.bitCount() - 2);
				do
				{
					Kernel.SquarePositive(bi, ref wkSpace);
					bi = Montgomery.Reduce(bi, this.mod, mPrime);
					if (exp.testBit(bitNum))
					{
						fixed (uint* ptr = &bi.data[0])
						{
							uint num = 0u;
							ulong num2 = 0uL;
							do
							{
								num2 = (ulong)((long)num2 + (long)ptr[num] * (long)b);
								ptr[num] = (uint)num2;
								num2 >>= 32;
							}
							while (++num < bi.length);
							if (bi.length < this.mod.length)
							{
								if (num2 != 0)
								{
									ptr[num] = (uint)num2;
									bi.length++;
									while (bi >= this.mod)
									{
										Kernel.MinusEq(bi, this.mod);
									}
								}
							}
							else if (num2 != 0)
							{
								uint num3 = (uint)num2;
								uint num4 = (uint)((((ulong)num3 << 32) | ptr[num - 1]) / (this.mod.data[this.mod.length - 1] + 1));
								num = 0u;
								num2 = 0uL;
								do
								{
									num2 = (ulong)((long)num2 + (long)this.mod.data[num] * (long)num4);
									uint num5 = ptr[num];
									ptr[num] -= (uint)(int)num2;
									num2 >>= 32;
									if (ptr[num] > num5)
									{
										num2++;
									}
									num++;
								}
								while (num < bi.length);
								num3 = (uint)((int)num3 - (int)num2);
								if (num3 != 0)
								{
									uint num6 = 0u;
									uint num7 = 0u;
									uint[] data = this.mod.data;
									do
									{
										uint num8 = data[num7];
										num6 = ((((num8 += num6) < num6) | ((ptr[num7] -= num8) > ~num8)) ? 1u : 0u);
										num7++;
									}
									while (num7 < bi.length);
									num3 -= num6;
								}
								while (bi >= this.mod)
								{
									Kernel.MinusEq(bi, this.mod);
								}
							}
							else
							{
								while (bi >= this.mod)
								{
									Kernel.MinusEq(bi, this.mod);
								}
							}
						}
					}
				}
				while (bitNum-- != 0);
				return Montgomery.Reduce(bi, this.mod, mPrime);
			}

			private unsafe BigInteger EvenPow(uint b, BigInteger exp)
			{
				exp.Normalize();
				uint[] wkSpace = new uint[this.mod.length << 2];
				BigInteger bigInteger = new BigInteger(b, this.mod.length << 2);
				uint bitNum = (uint)(exp.bitCount() - 2);
				do
				{
					Kernel.SquarePositive(bigInteger, ref wkSpace);
					if (bigInteger.length >= this.mod.length)
					{
						BarrettReduction(bigInteger);
					}
					if (exp.testBit(bitNum))
					{
						fixed (uint* ptr = &bigInteger.data[0])
						{
							uint num = 0u;
							ulong num2 = 0uL;
							do
							{
								num2 = (ulong)((long)num2 + (long)ptr[num] * (long)b);
								ptr[num] = (uint)num2;
								num2 >>= 32;
							}
							while (++num < bigInteger.length);
							if (bigInteger.length < this.mod.length)
							{
								if (num2 != 0)
								{
									ptr[num] = (uint)num2;
									bigInteger.length++;
									while (bigInteger >= this.mod)
									{
										Kernel.MinusEq(bigInteger, this.mod);
									}
								}
							}
							else if (num2 != 0)
							{
								uint num3 = (uint)num2;
								uint num4 = (uint)((((ulong)num3 << 32) | ptr[num - 1]) / (this.mod.data[this.mod.length - 1] + 1));
								num = 0u;
								num2 = 0uL;
								do
								{
									num2 = (ulong)((long)num2 + (long)this.mod.data[num] * (long)num4);
									uint num5 = ptr[num];
									ptr[num] -= (uint)(int)num2;
									num2 >>= 32;
									if (ptr[num] > num5)
									{
										num2++;
									}
									num++;
								}
								while (num < bigInteger.length);
								num3 = (uint)((int)num3 - (int)num2);
								if (num3 != 0)
								{
									uint num6 = 0u;
									uint num7 = 0u;
									uint[] data = this.mod.data;
									do
									{
										uint num8 = data[num7];
										num6 = ((((num8 += num6) < num6) | ((ptr[num7] -= num8) > ~num8)) ? 1u : 0u);
										num7++;
									}
									while (num7 < bigInteger.length);
									num3 -= num6;
								}
								while (bigInteger >= this.mod)
								{
									Kernel.MinusEq(bigInteger, this.mod);
								}
							}
							else
							{
								while (bigInteger >= this.mod)
								{
									Kernel.MinusEq(bigInteger, this.mod);
								}
							}
						}
					}
				}
				while (bitNum-- != 0);
				return bigInteger;
			}

			private unsafe BigInteger EvenModTwoPow(BigInteger exp)
			{
				exp.Normalize();
				uint[] wkSpace = new uint[this.mod.length << 2];
				BigInteger bigInteger = new BigInteger(2, this.mod.length << 2);
				uint num = exp.data[exp.length - 1];
				uint num2 = 2147483648u;
				while ((num & num2) == 0)
				{
					num2 >>= 1;
				}
				num2 >>= 1;
				uint num3 = exp.length - 1;
				do
				{
					num = exp.data[num3];
					do
					{
						Kernel.SquarePositive(bigInteger, ref wkSpace);
						if (bigInteger.length >= this.mod.length)
						{
							BarrettReduction(bigInteger);
						}
						if ((num & num2) != 0)
						{
							fixed (uint* ptr = &bigInteger.data[0])
							{
								uint* ptr2 = ptr;
								uint* ptr3 = ptr + bigInteger.length;
								uint num4 = 0u;
								for (; ptr2 < ptr3; ptr2++)
								{
									uint num5 = *ptr2;
									*ptr2 = ((num5 << 1) | num4);
									num4 = num5 >> 31;
								}
								if (num4 != 0 || bigInteger >= this.mod)
								{
									ptr2 = ptr;
									uint num6 = 0u;
									uint[] data = this.mod.data;
									uint num7 = 0u;
									do
									{
										uint num8 = data[num7];
										bool num9 = (num8 += num6) < num6;
										uint* intPtr = ptr2;
										ptr2 = intPtr + 1;
										num6 = ((num9 | ((*intPtr -= num8) > ~num8)) ? 1u : 0u);
										num7++;
									}
									while (ptr2 < ptr3);
								}
							}
						}
					}
					while ((num2 >>= 1) != 0);
					num2 = 2147483648u;
				}
				while (num3-- != 0);
				return bigInteger;
			}

			private unsafe BigInteger OddModTwoPow(BigInteger exp)
			{
				uint[] wkSpace = new uint[this.mod.length << 2];
				BigInteger bi = Montgomery.ToMont(2, this.mod);
				bi = new BigInteger(bi, this.mod.length << 2);
				uint mPrime = Montgomery.Inverse(this.mod.data[0]);
				uint bitNum = (uint)(exp.bitCount() - 2);
				do
				{
					Kernel.SquarePositive(bi, ref wkSpace);
					bi = Montgomery.Reduce(bi, this.mod, mPrime);
					if (exp.testBit(bitNum))
					{
						fixed (uint* ptr = &bi.data[0])
						{
							uint* ptr2 = ptr;
							uint* ptr3 = ptr + bi.length;
							uint num = 0u;
							for (; ptr2 < ptr3; ptr2++)
							{
								uint num2 = *ptr2;
								*ptr2 = ((num2 << 1) | num);
								num = num2 >> 31;
							}
							if (num != 0 || bi >= this.mod)
							{
								fixed (uint* ptr4 = &this.mod.data[0])
								{
									ptr2 = ptr;
									uint num3 = 0u;
									uint* ptr5 = ptr4;
									do
									{
										uint* intPtr = ptr5;
										ptr5 = intPtr + 1;
										uint num4 = *intPtr;
										bool num5 = (num4 += num3) < num3;
										uint* intPtr2 = ptr2;
										ptr2 = intPtr2 + 1;
										num3 = ((num5 | ((*intPtr2 -= num4) > ~num4)) ? 1u : 0u);
									}
									while (ptr2 < ptr3);
								}
							}
						}
					}
				}
				while (bitNum-- != 0);
				return Montgomery.Reduce(bi, this.mod, mPrime);
			}
		}

		public sealed class Montgomery
		{
			public static uint Inverse(uint n)
			{
				uint num = n;
				uint num2;
				while ((num2 = n * num) != 1)
				{
					num *= 2 - num2;
				}
				return (uint)(0L - num);
			}

			public static BigInteger ToMont(BigInteger n, BigInteger m)
			{
				n.Normalize();
				m.Normalize();
				n <<= (int)(m.length * 32);
				n %= m;
				return n;
			}

			public unsafe static BigInteger Reduce(BigInteger n, BigInteger m, uint mPrime)
			{
				fixed (uint* ptr = &n.data[0])
				{
					fixed (uint* ptr2 = &m.data[0])
					{
						for (uint num = 0u; num < m.length; num++)
						{
							uint num2 = *ptr * mPrime;
							uint* ptr3 = ptr2;
							uint* ptr4 = ptr;
							uint* ptr5 = ptr;
							long num3 = num2;
							uint* intPtr = ptr3;
							ptr3 = intPtr + 1;
							long num4 = num3 * *intPtr;
							uint* intPtr2 = ptr4;
							ptr4 = intPtr2 + 1;
							ulong num5 = (ulong)(num4 + *intPtr2);
							num5 >>= 32;
							uint num6;
							for (num6 = 1u; num6 < m.length; num6++)
							{
								ulong num7 = num5;
								long num8 = num2;
								uint* intPtr3 = ptr3;
								ptr3 = intPtr3 + 1;
								long num9 = num8 * *intPtr3;
								uint* intPtr4 = ptr4;
								ptr4 = intPtr4 + 1;
								num5 = (ulong)((long)num7 + (num9 + *intPtr4));
								uint* intPtr5 = ptr5;
								ptr5 = intPtr5 + 1;
								*intPtr5 = (uint)num5;
								num5 >>= 32;
							}
							for (; num6 < n.length; num6++)
							{
								ulong num10 = num5;
								uint* intPtr6 = ptr4;
								ptr4 = intPtr6 + 1;
								num5 = num10 + *intPtr6;
								uint* intPtr7 = ptr5;
								ptr5 = intPtr7 + 1;
								*intPtr7 = (uint)num5;
								num5 >>= 32;
								if (num5 == 0)
								{
									num6++;
									break;
								}
							}
							for (; num6 < n.length; num6++)
							{
								uint* intPtr8 = ptr5;
								ptr5 = intPtr8 + 1;
								uint* intPtr9 = ptr4;
								ptr4 = intPtr9 + 1;
								*intPtr8 = *intPtr9;
							}
							uint* intPtr10 = ptr5;
							ptr5 = intPtr10 + 1;
							*intPtr10 = (uint)num5;
						}
						while (n.length > 1 && ptr[n.length - 1] == 0)
						{
							n.length--;
						}
					}
				}
				if (n >= m)
				{
					Kernel.MinusEq(n, m);
				}
				return n;
			}

			public static BigInteger Reduce(BigInteger n, BigInteger m)
			{
				return Reduce(n, m, Inverse(m.data[0]));
			}
		}

		private sealed class Kernel
		{
			public static BigInteger AddSameSign(BigInteger bi1, BigInteger bi2)
			{
				uint num = 0u;
				uint[] data;
				uint length;
				uint[] data2;
				uint length2;
				if (bi1.length < bi2.length)
				{
					data = bi2.data;
					length = bi2.length;
					data2 = bi1.data;
					length2 = bi1.length;
				}
				else
				{
					data = bi1.data;
					length = bi1.length;
					data2 = bi2.data;
					length2 = bi2.length;
				}
				BigInteger bigInteger = new BigInteger(Sign.Positive, length + 1);
				uint[] data3 = bigInteger.data;
				ulong num2 = 0uL;
				do
				{
					num2 = (ulong)((long)data[num] + (long)data2[num] + (long)num2);
					data3[num] = (uint)num2;
					num2 >>= 32;
				}
				while (++num < length2);
				bool flag = num2 != 0;
				if (flag)
				{
					if (num < length)
					{
						do
						{
							flag = ((data3[num] = data[num] + 1) == 0);
						}
						while (++num < length && flag);
					}
					if (flag)
					{
						data3[num] = 1u;
						num = (bigInteger.length = num + 1);
						return bigInteger;
					}
				}
				if (num < length)
				{
					do
					{
						data3[num] = data[num];
					}
					while (++num < length);
				}
				bigInteger.Normalize();
				return bigInteger;
			}

			public static BigInteger Subtract(BigInteger big, BigInteger small)
			{
				BigInteger bigInteger = new BigInteger(Sign.Positive, big.length);
				uint[] data = bigInteger.data;
				uint[] data2 = big.data;
				uint[] data3 = small.data;
				uint num = 0u;
				uint num2 = 0u;
				do
				{
					uint num3 = data3[num];
					num2 = ((((num3 += num2) < num2) | ((data[num] = data2[num] - num3) > ~num3)) ? 1u : 0u);
				}
				while (++num < small.length);
				if (num != big.length)
				{
					if (num2 == 1)
					{
						do
						{
							data[num] = data2[num] - 1;
						}
						while (data2[num++] == 0 && num < big.length);
						if (num == big.length)
						{
							goto IL_00c0;
						}
					}
					do
					{
						data[num] = data2[num];
					}
					while (++num < big.length);
				}
				goto IL_00c0;
				IL_00c0:
				bigInteger.Normalize();
				return bigInteger;
			}

			public unsafe static void MinusEq(BigInteger big, BigInteger small)
			{
				uint[] data = big.data;
				uint[] data2 = small.data;
				uint num = 0u;
				uint num2 = 0u;
				do
				{
					uint num3 = data2[num];
					uint[] array;
					IntPtr intPtr;
					num2 = ((((num3 += num2) < num2) | (((array = data)[(long)(intPtr = (IntPtr)(void*)num)] = array[(long)intPtr] - num3) > ~num3)) ? 1u : 0u);
				}
				while (++num < small.length);
				if (num != big.length && num2 == 1)
				{
					do
					{
						uint[] array;
						IntPtr intPtr;
						(array = data)[(long)(intPtr = (IntPtr)(void*)num)] = array[(long)intPtr] - 1;
					}
					while (data[num++] == 0 && num < big.length);
				}
				while (big.length != 0 && big.data[big.length - 1] == 0)
				{
					big.length--;
				}
				if (big.length == 0)
				{
					big.length++;
				}
			}

			public static void PlusEq(BigInteger bi1, BigInteger bi2)
			{
				uint num = 0u;
				bool flag = false;
				uint[] data;
				uint length;
				uint[] data2;
				uint length2;
				if (bi1.length < bi2.length)
				{
					flag = true;
					data = bi2.data;
					length = bi2.length;
					data2 = bi1.data;
					length2 = bi1.length;
				}
				else
				{
					data = bi1.data;
					length = bi1.length;
					data2 = bi2.data;
					length2 = bi2.length;
				}
				uint[] data3 = bi1.data;
				ulong num2 = 0uL;
				do
				{
					num2 = (ulong)((long)num2 + ((long)data[num] + (long)data2[num]));
					data3[num] = (uint)num2;
					num2 >>= 32;
				}
				while (++num < length2);
				bool flag2 = num2 != 0;
				if (flag2)
				{
					if (num < length)
					{
						do
						{
							flag2 = ((data3[num] = data[num] + 1) == 0);
						}
						while (++num < length && flag2);
					}
					if (flag2)
					{
						data3[num] = 1u;
						num = (bi1.length = num + 1);
						return;
					}
				}
				if (flag && num < length - 1)
				{
					do
					{
						data3[num] = data[num];
					}
					while (++num < length);
				}
				bi1.length = length + 1;
				bi1.Normalize();
			}

			public static Sign Compare(BigInteger bi1, BigInteger bi2)
			{
				uint num = bi1.length;
				uint num2 = bi2.length;
				while (num != 0 && bi1.data[num - 1] == 0)
				{
					num--;
				}
				while (num2 != 0 && bi2.data[num2 - 1] == 0)
				{
					num2--;
				}
				if (num == 0 && num2 == 0)
				{
					return Sign.Zero;
				}
				if (num < num2)
				{
					return Sign.Negative;
				}
				if (num > num2)
				{
					return Sign.Positive;
				}
				uint num3 = num - 1;
				while (num3 != 0 && bi1.data[num3] == bi2.data[num3])
				{
					num3--;
				}
				if (bi1.data[num3] < bi2.data[num3])
				{
					return Sign.Negative;
				}
				if (bi1.data[num3] > bi2.data[num3])
				{
					return Sign.Positive;
				}
				return Sign.Zero;
			}

			public static uint SingleByteDivideInPlace(BigInteger n, uint d)
			{
				ulong num = 0uL;
				uint length = n.length;
				while (length-- != 0)
				{
					num <<= 32;
					num |= n.data[length];
					n.data[length] = (uint)(num / d);
					num %= d;
				}
				n.Normalize();
				return (uint)num;
			}

			public static uint DwordMod(BigInteger n, uint d)
			{
				ulong num = 0uL;
				uint length = n.length;
				while (length-- != 0)
				{
					num <<= 32;
					num |= n.data[length];
					num %= d;
				}
				return (uint)num;
			}

			public static BigInteger DwordDiv(BigInteger n, uint d)
			{
				BigInteger bigInteger = new BigInteger(Sign.Positive, n.length);
				ulong num = 0uL;
				uint length = n.length;
				while (length-- != 0)
				{
					num <<= 32;
					num |= n.data[length];
					bigInteger.data[length] = (uint)(num / d);
					num %= d;
				}
				bigInteger.Normalize();
				return bigInteger;
			}

			public static BigInteger[] DwordDivMod(BigInteger n, uint d)
			{
				BigInteger bigInteger = new BigInteger(Sign.Positive, n.length);
				ulong num = 0uL;
				uint length = n.length;
				while (length-- != 0)
				{
					num <<= 32;
					num |= n.data[length];
					bigInteger.data[length] = (uint)(num / d);
					num %= d;
				}
				bigInteger.Normalize();
				BigInteger bigInteger2 = (uint)num;
				return new BigInteger[2]
				{
					bigInteger,
					bigInteger2
				};
			}

			public static BigInteger[] multiByteDivide(BigInteger bi1, BigInteger bi2)
			{
				if (Compare(bi1, bi2) == Sign.Negative)
				{
					return new BigInteger[2]
					{
						0,
						new BigInteger(bi1)
					};
				}
				bi1.Normalize();
				bi2.Normalize();
				if (bi2.length == 1)
				{
					return DwordDivMod(bi1, bi2.data[0]);
				}
				uint num = bi1.length + 1;
				int num2 = (int)(bi2.length + 1);
				uint num3 = 2147483648u;
				uint num4 = bi2.data[bi2.length - 1];
				int num5 = 0;
				int num6 = (int)(bi1.length - bi2.length);
				while (num3 != 0 && (num4 & num3) == 0)
				{
					num5++;
					num3 >>= 1;
				}
				BigInteger bigInteger = new BigInteger(Sign.Positive, bi1.length - bi2.length + 1);
				BigInteger bigInteger2 = bi1 << num5;
				uint[] data = bigInteger2.data;
				bi2 <<= num5;
				int num7 = (int)(num - bi2.length);
				int num8 = (int)(num - 1);
				uint num9 = bi2.data[bi2.length - 1];
				ulong num10 = bi2.data[bi2.length - 2];
				while (num7 > 0)
				{
					ulong num11 = ((ulong)data[num8] << 32) + data[num8 - 1];
					ulong num12 = num11 / num9;
					ulong num13 = num11 % num9;
					while (num12 == 4294967296L || num12 * num10 > (num13 << 32) + data[num8 - 2])
					{
						num12--;
						num13 += num9;
						if (num13 >= 4294967296L)
						{
							break;
						}
					}
					uint num14 = 0u;
					int num15 = num8 - num2 + 1;
					ulong num16 = 0uL;
					uint num17 = (uint)num12;
					do
					{
						num16 = (ulong)((long)num16 + (long)bi2.data[num14] * (long)num17);
						uint num18 = data[num15];
						uint[] array;
						uint[] array2 = array = data;
						int num19 = num15;
						IntPtr intPtr = (IntPtr)num19;
						array2[num19] = (uint)((int)array[(long)intPtr] - (int)num16);
						num16 >>= 32;
						if (data[num15] > num18)
						{
							num16++;
						}
						num14++;
						num15++;
					}
					while (num14 < num2);
					num15 = num8 - num2 + 1;
					num14 = 0u;
					if (num16 != 0)
					{
						num17--;
						ulong num20 = 0uL;
						do
						{
							num20 = (ulong)((long)data[num15] + (long)bi2.data[num14] + (long)num20);
							data[num15] = (uint)num20;
							num20 >>= 32;
							num14++;
							num15++;
						}
						while (num14 < num2);
					}
					bigInteger.data[num6--] = num17;
					num8--;
					num7--;
				}
				bigInteger.Normalize();
				bigInteger2.Normalize();
				BigInteger[] array3 = new BigInteger[2]
				{
					bigInteger,
					bigInteger2
				};
				if (num5 != 0)
				{
					BigInteger[] array4;
					(array4 = array3)[1] = array4[1] >> num5;
				}
				return array3;
			}

			public static BigInteger LeftShift(BigInteger bi, int n)
			{
				if (n == 0)
				{
					return new BigInteger(bi, bi.length + 1);
				}
				int num = n >> 5;
				n &= 0x1F;
				BigInteger bigInteger = new BigInteger(Sign.Positive, (uint)((int)(bi.length + 1) + num));
				uint num2 = 0u;
				uint length = bi.length;
				if (n != 0)
				{
					uint num3 = 0u;
					for (; num2 < length; num2++)
					{
						uint num4 = bi.data[num2];
						bigInteger.data[num2 + num] = ((num4 << n) | num3);
						num3 = num4 >> 32 - n;
					}
					bigInteger.data[num2 + num] = num3;
				}
				else
				{
					for (; num2 < length; num2++)
					{
						bigInteger.data[num2 + num] = bi.data[num2];
					}
				}
				bigInteger.Normalize();
				return bigInteger;
			}

			public static BigInteger RightShift(BigInteger bi, int n)
			{
				if (n == 0)
				{
					return new BigInteger(bi);
				}
				int num = n >> 5;
				int num2 = n & 0x1F;
				BigInteger bigInteger = new BigInteger(Sign.Positive, (uint)((int)bi.length - num + 1));
				uint num3 = (uint)(bigInteger.data.Length - 1);
				if (num2 != 0)
				{
					uint num4 = 0u;
					while (num3-- != 0)
					{
						uint num5 = bi.data[num3 + num];
						bigInteger.data[num3] = ((num5 >> n) | num4);
						num4 = num5 << 32 - n;
					}
				}
				else
				{
					while (num3-- != 0)
					{
						bigInteger.data[num3] = bi.data[num3 + num];
					}
				}
				bigInteger.Normalize();
				return bigInteger;
			}

			public static BigInteger MultiplyByDword(BigInteger n, uint f)
			{
				BigInteger bigInteger = new BigInteger(Sign.Positive, n.length + 1);
				uint num = 0u;
				ulong num2 = 0uL;
				do
				{
					num2 = (ulong)((long)num2 + (long)n.data[num] * (long)f);
					bigInteger.data[num] = (uint)num2;
					num2 >>= 32;
				}
				while (++num < n.length);
				bigInteger.data[num] = (uint)num2;
				bigInteger.Normalize();
				return bigInteger;
			}

			public unsafe static void Multiply(uint[] x, uint xOffset, uint xLen, uint[] y, uint yOffset, uint yLen, uint[] d, uint dOffset)
			{
				fixed (uint* ptr = &x[0])
				{
					fixed (uint* ptr4 = &y[0])
					{
						fixed (uint* ptr7 = &d[0])
						{
							uint* ptr2 = ptr + xOffset;
							uint* ptr3 = ptr2 + xLen;
							uint* ptr5 = ptr4 + yOffset;
							uint* ptr6 = ptr5 + yLen;
							uint* ptr8 = ptr7 + dOffset;
							while (ptr2 < ptr3)
							{
								if (*ptr2 != 0)
								{
									ulong num = 0uL;
									uint* ptr9 = ptr8;
									uint* ptr10 = ptr5;
									while (ptr10 < ptr6)
									{
										num = (ulong)((long)num + ((long)(*ptr2) * (long)(*ptr10) + *ptr9));
										*ptr9 = (uint)num;
										num >>= 32;
										ptr10++;
										ptr9++;
									}
									if (num != 0)
									{
										*ptr9 = (uint)num;
									}
								}
								ptr2++;
								ptr8++;
							}
						}
					}
				}
			}

			public unsafe static void MultiplyMod2p32pmod(uint[] x, int xOffset, int xLen, uint[] y, int yOffest, int yLen, uint[] d, int dOffset, int mod)
			{
				fixed (uint* ptr = &x[0])
				{
					fixed (uint* ptr4 = &y[0])
					{
						fixed (uint* ptr7 = &d[0])
						{
							uint* ptr2 = ptr + xOffset;
							uint* ptr3 = ptr2 + xLen;
							uint* ptr5 = ptr4 + yOffest;
							uint* ptr6 = ptr5 + yLen;
							uint* ptr8 = ptr7 + dOffset;
							uint* ptr9 = ptr8 + mod;
							while (ptr2 < ptr3)
							{
								if (*ptr2 != 0)
								{
									ulong num = 0uL;
									uint* ptr10 = ptr8;
									uint* ptr11 = ptr5;
									while (ptr11 < ptr6 && ptr10 < ptr9)
									{
										num = (ulong)((long)num + ((long)(*ptr2) * (long)(*ptr11) + *ptr10));
										*ptr10 = (uint)num;
										num >>= 32;
										ptr11++;
										ptr10++;
									}
									if (num != 0 && ptr10 < ptr9)
									{
										*ptr10 = (uint)num;
									}
								}
								ptr2++;
								ptr8++;
							}
						}
					}
				}
			}

			public unsafe static void SquarePositive(BigInteger bi, ref uint[] wkSpace)
			{
				uint[] array = wkSpace;
				wkSpace = bi.data;
				uint[] data = bi.data;
				uint length = bi.length;
				bi.data = array;
				fixed (uint* ptr4 = &data[0])
				{
					fixed (uint* ptr = &array[0])
					{
						uint* ptr2 = ptr + array.Length;
						for (uint* ptr3 = ptr; ptr3 < ptr2; ptr3++)
						{
							*ptr3 = 0u;
						}
						uint* ptr5 = ptr4;
						uint* ptr6 = ptr;
						uint num = 0u;
						while (num < length)
						{
							if (*ptr5 != 0)
							{
								ulong num2 = 0uL;
								uint num3 = *ptr5;
								uint* ptr7 = ptr5 + 1;
								uint* ptr8 = ptr6 + 2 * num + 1;
								uint num4 = num + 1;
								while (num4 < length)
								{
									num2 = (ulong)((long)num2 + ((long)num3 * (long)(*ptr7) + *ptr8));
									*ptr8 = (uint)num2;
									num2 >>= 32;
									num4++;
									ptr8++;
									ptr7++;
								}
								if (num2 != 0)
								{
									*ptr8 = (uint)num2;
								}
							}
							num++;
							ptr5++;
						}
						ptr6 = ptr;
						uint num5 = 0u;
						for (; ptr6 < ptr2; ptr6++)
						{
							uint num6 = *ptr6;
							*ptr6 = ((num6 << 1) | num5);
							num5 = num6 >> 31;
						}
						if (num5 != 0)
						{
							*ptr6 = num5;
						}
						ptr5 = ptr4;
						ptr6 = ptr;
						uint* ptr9 = ptr5 + length;
						while (ptr5 < ptr9)
						{
							ulong num7 = (ulong)((long)(*ptr5) * (long)(*ptr5) + *ptr6);
							*ptr6 = (uint)num7;
							num7 >>= 32;
							*(++ptr6) += (uint)(int)num7;
							if (*ptr6 < (uint)num7)
							{
								uint* ptr10 = ptr6;
								(*(++ptr10))++;
								while (true)
								{
									uint* intPtr = ptr10;
									ptr10 = intPtr + 1;
									if (*intPtr != 0)
									{
										break;
									}
									(*ptr10)++;
								}
							}
							ptr5++;
							ptr6++;
						}
						bi.length <<= 1;
						while (ptr[bi.length - 1] == 0 && bi.length > 1)
						{
							bi.length--;
						}
					}
				}
			}

			public static bool Double(uint[] u, int l)
			{
				uint num = 0u;
				for (uint num2 = 0u; num2 < l; num2++)
				{
					uint num3 = u[num2];
					u[num2] = ((num3 << 1) | num);
					num = num3 >> 31;
				}
				if (num != 0)
				{
					u[l] = num;
				}
				return num != 0;
			}

			public static BigInteger gcd(BigInteger a, BigInteger b)
			{
				BigInteger bigInteger = a;
				BigInteger bigInteger2 = b;
				BigInteger bigInteger3 = bigInteger2;
				while (bigInteger.length > 1)
				{
					bigInteger3 = bigInteger;
					bigInteger = bigInteger2 % bigInteger;
					bigInteger2 = bigInteger3;
				}
				if (bigInteger == 0u)
				{
					return bigInteger3;
				}
				uint num = bigInteger.data[0];
				uint num2 = bigInteger2 % num;
				int num3 = 0;
				while (((num2 | num) & 1) == 0)
				{
					num2 >>= 1;
					num >>= 1;
					num3++;
				}
				while (num2 != 0)
				{
					while ((num2 & 1) == 0)
					{
						num2 >>= 1;
					}
					while ((num & 1) == 0)
					{
						num >>= 1;
					}
					if (num2 >= num)
					{
						num2 = num2 - num >> 1;
					}
					else
					{
						num = num - num2 >> 1;
					}
				}
				return num << num3;
			}

			public static uint modInverse(BigInteger bi, uint modulus)
			{
				uint num = modulus;
				uint num2 = bi % modulus;
				uint num3 = 0u;
				uint num4 = 1u;
				while (true)
				{
					switch (num2)
					{
					case 1u:
						return num4;
					default:
						num3 += num / num2 * num4;
						num %= num2;
						switch (num)
						{
						case 1u:
							return modulus - num3;
						default:
							goto IL_002d;
						case 0u:
							break;
						}
						break;
					case 0u:
						break;
					}
					break;
					IL_002d:
					num4 += num2 / num * num3;
					num2 %= num;
				}
				return 0u;
			}

			public static BigInteger modInverse(BigInteger bi, BigInteger modulus)
			{
				if (modulus.length == 1)
				{
					return modInverse(bi, modulus.data[0]);
				}
				BigInteger[] array = new BigInteger[2]
				{
					0,
					1
				};
				BigInteger[] array2 = new BigInteger[2];
				BigInteger[] array3 = new BigInteger[2]
				{
					0,
					0
				};
				int num = 0;
				BigInteger bi2 = modulus;
				BigInteger bigInteger = bi;
				ModulusRing modulusRing = new ModulusRing(modulus);
				while (bigInteger != 0u)
				{
					if (num > 1)
					{
						BigInteger bigInteger2 = modulusRing.Difference(array[0], array[1] * array2[0]);
						array[0] = array[1];
						array[1] = bigInteger2;
					}
					BigInteger[] array4 = multiByteDivide(bi2, bigInteger);
					array2[0] = array2[1];
					array2[1] = array4[0];
					array3[0] = array3[1];
					array3[1] = array4[1];
					bi2 = bigInteger;
					bigInteger = array4[1];
					num++;
				}
				if (array3[0] != 1u)
				{
					throw new ArithmeticException("No inverse!");
				}
				return modulusRing.Difference(array[0], array[1] * array2[0]);
			}
		}

		private const uint DEFAULT_LEN = 20u;

		private const string WouldReturnNegVal = "Operation would return a negative value";

		private uint length = 1u;

		private uint[] data;

		public static readonly uint[] smallPrimes = new uint[783]
		{
			2u,
			3u,
			5u,
			7u,
			11u,
			13u,
			17u,
			19u,
			23u,
			29u,
			31u,
			37u,
			41u,
			43u,
			47u,
			53u,
			59u,
			61u,
			67u,
			71u,
			73u,
			79u,
			83u,
			89u,
			97u,
			101u,
			103u,
			107u,
			109u,
			113u,
			127u,
			131u,
			137u,
			139u,
			149u,
			151u,
			157u,
			163u,
			167u,
			173u,
			179u,
			181u,
			191u,
			193u,
			197u,
			199u,
			211u,
			223u,
			227u,
			229u,
			233u,
			239u,
			241u,
			251u,
			257u,
			263u,
			269u,
			271u,
			277u,
			281u,
			283u,
			293u,
			307u,
			311u,
			313u,
			317u,
			331u,
			337u,
			347u,
			349u,
			353u,
			359u,
			367u,
			373u,
			379u,
			383u,
			389u,
			397u,
			401u,
			409u,
			419u,
			421u,
			431u,
			433u,
			439u,
			443u,
			449u,
			457u,
			461u,
			463u,
			467u,
			479u,
			487u,
			491u,
			499u,
			503u,
			509u,
			521u,
			523u,
			541u,
			547u,
			557u,
			563u,
			569u,
			571u,
			577u,
			587u,
			593u,
			599u,
			601u,
			607u,
			613u,
			617u,
			619u,
			631u,
			641u,
			643u,
			647u,
			653u,
			659u,
			661u,
			673u,
			677u,
			683u,
			691u,
			701u,
			709u,
			719u,
			727u,
			733u,
			739u,
			743u,
			751u,
			757u,
			761u,
			769u,
			773u,
			787u,
			797u,
			809u,
			811u,
			821u,
			823u,
			827u,
			829u,
			839u,
			853u,
			857u,
			859u,
			863u,
			877u,
			881u,
			883u,
			887u,
			907u,
			911u,
			919u,
			929u,
			937u,
			941u,
			947u,
			953u,
			967u,
			971u,
			977u,
			983u,
			991u,
			997u,
			1009u,
			1013u,
			1019u,
			1021u,
			1031u,
			1033u,
			1039u,
			1049u,
			1051u,
			1061u,
			1063u,
			1069u,
			1087u,
			1091u,
			1093u,
			1097u,
			1103u,
			1109u,
			1117u,
			1123u,
			1129u,
			1151u,
			1153u,
			1163u,
			1171u,
			1181u,
			1187u,
			1193u,
			1201u,
			1213u,
			1217u,
			1223u,
			1229u,
			1231u,
			1237u,
			1249u,
			1259u,
			1277u,
			1279u,
			1283u,
			1289u,
			1291u,
			1297u,
			1301u,
			1303u,
			1307u,
			1319u,
			1321u,
			1327u,
			1361u,
			1367u,
			1373u,
			1381u,
			1399u,
			1409u,
			1423u,
			1427u,
			1429u,
			1433u,
			1439u,
			1447u,
			1451u,
			1453u,
			1459u,
			1471u,
			1481u,
			1483u,
			1487u,
			1489u,
			1493u,
			1499u,
			1511u,
			1523u,
			1531u,
			1543u,
			1549u,
			1553u,
			1559u,
			1567u,
			1571u,
			1579u,
			1583u,
			1597u,
			1601u,
			1607u,
			1609u,
			1613u,
			1619u,
			1621u,
			1627u,
			1637u,
			1657u,
			1663u,
			1667u,
			1669u,
			1693u,
			1697u,
			1699u,
			1709u,
			1721u,
			1723u,
			1733u,
			1741u,
			1747u,
			1753u,
			1759u,
			1777u,
			1783u,
			1787u,
			1789u,
			1801u,
			1811u,
			1823u,
			1831u,
			1847u,
			1861u,
			1867u,
			1871u,
			1873u,
			1877u,
			1879u,
			1889u,
			1901u,
			1907u,
			1913u,
			1931u,
			1933u,
			1949u,
			1951u,
			1973u,
			1979u,
			1987u,
			1993u,
			1997u,
			1999u,
			2003u,
			2011u,
			2017u,
			2027u,
			2029u,
			2039u,
			2053u,
			2063u,
			2069u,
			2081u,
			2083u,
			2087u,
			2089u,
			2099u,
			2111u,
			2113u,
			2129u,
			2131u,
			2137u,
			2141u,
			2143u,
			2153u,
			2161u,
			2179u,
			2203u,
			2207u,
			2213u,
			2221u,
			2237u,
			2239u,
			2243u,
			2251u,
			2267u,
			2269u,
			2273u,
			2281u,
			2287u,
			2293u,
			2297u,
			2309u,
			2311u,
			2333u,
			2339u,
			2341u,
			2347u,
			2351u,
			2357u,
			2371u,
			2377u,
			2381u,
			2383u,
			2389u,
			2393u,
			2399u,
			2411u,
			2417u,
			2423u,
			2437u,
			2441u,
			2447u,
			2459u,
			2467u,
			2473u,
			2477u,
			2503u,
			2521u,
			2531u,
			2539u,
			2543u,
			2549u,
			2551u,
			2557u,
			2579u,
			2591u,
			2593u,
			2609u,
			2617u,
			2621u,
			2633u,
			2647u,
			2657u,
			2659u,
			2663u,
			2671u,
			2677u,
			2683u,
			2687u,
			2689u,
			2693u,
			2699u,
			2707u,
			2711u,
			2713u,
			2719u,
			2729u,
			2731u,
			2741u,
			2749u,
			2753u,
			2767u,
			2777u,
			2789u,
			2791u,
			2797u,
			2801u,
			2803u,
			2819u,
			2833u,
			2837u,
			2843u,
			2851u,
			2857u,
			2861u,
			2879u,
			2887u,
			2897u,
			2903u,
			2909u,
			2917u,
			2927u,
			2939u,
			2953u,
			2957u,
			2963u,
			2969u,
			2971u,
			2999u,
			3001u,
			3011u,
			3019u,
			3023u,
			3037u,
			3041u,
			3049u,
			3061u,
			3067u,
			3079u,
			3083u,
			3089u,
			3109u,
			3119u,
			3121u,
			3137u,
			3163u,
			3167u,
			3169u,
			3181u,
			3187u,
			3191u,
			3203u,
			3209u,
			3217u,
			3221u,
			3229u,
			3251u,
			3253u,
			3257u,
			3259u,
			3271u,
			3299u,
			3301u,
			3307u,
			3313u,
			3319u,
			3323u,
			3329u,
			3331u,
			3343u,
			3347u,
			3359u,
			3361u,
			3371u,
			3373u,
			3389u,
			3391u,
			3407u,
			3413u,
			3433u,
			3449u,
			3457u,
			3461u,
			3463u,
			3467u,
			3469u,
			3491u,
			3499u,
			3511u,
			3517u,
			3527u,
			3529u,
			3533u,
			3539u,
			3541u,
			3547u,
			3557u,
			3559u,
			3571u,
			3581u,
			3583u,
			3593u,
			3607u,
			3613u,
			3617u,
			3623u,
			3631u,
			3637u,
			3643u,
			3659u,
			3671u,
			3673u,
			3677u,
			3691u,
			3697u,
			3701u,
			3709u,
			3719u,
			3727u,
			3733u,
			3739u,
			3761u,
			3767u,
			3769u,
			3779u,
			3793u,
			3797u,
			3803u,
			3821u,
			3823u,
			3833u,
			3847u,
			3851u,
			3853u,
			3863u,
			3877u,
			3881u,
			3889u,
			3907u,
			3911u,
			3917u,
			3919u,
			3923u,
			3929u,
			3931u,
			3943u,
			3947u,
			3967u,
			3989u,
			4001u,
			4003u,
			4007u,
			4013u,
			4019u,
			4021u,
			4027u,
			4049u,
			4051u,
			4057u,
			4073u,
			4079u,
			4091u,
			4093u,
			4099u,
			4111u,
			4127u,
			4129u,
			4133u,
			4139u,
			4153u,
			4157u,
			4159u,
			4177u,
			4201u,
			4211u,
			4217u,
			4219u,
			4229u,
			4231u,
			4241u,
			4243u,
			4253u,
			4259u,
			4261u,
			4271u,
			4273u,
			4283u,
			4289u,
			4297u,
			4327u,
			4337u,
			4339u,
			4349u,
			4357u,
			4363u,
			4373u,
			4391u,
			4397u,
			4409u,
			4421u,
			4423u,
			4441u,
			4447u,
			4451u,
			4457u,
			4463u,
			4481u,
			4483u,
			4493u,
			4507u,
			4513u,
			4517u,
			4519u,
			4523u,
			4547u,
			4549u,
			4561u,
			4567u,
			4583u,
			4591u,
			4597u,
			4603u,
			4621u,
			4637u,
			4639u,
			4643u,
			4649u,
			4651u,
			4657u,
			4663u,
			4673u,
			4679u,
			4691u,
			4703u,
			4721u,
			4723u,
			4729u,
			4733u,
			4751u,
			4759u,
			4783u,
			4787u,
			4789u,
			4793u,
			4799u,
			4801u,
			4813u,
			4817u,
			4831u,
			4861u,
			4871u,
			4877u,
			4889u,
			4903u,
			4909u,
			4919u,
			4931u,
			4933u,
			4937u,
			4943u,
			4951u,
			4957u,
			4967u,
			4969u,
			4973u,
			4987u,
			4993u,
			4999u,
			5003u,
			5009u,
			5011u,
			5021u,
			5023u,
			5039u,
			5051u,
			5059u,
			5077u,
			5081u,
			5087u,
			5099u,
			5101u,
			5107u,
			5113u,
			5119u,
			5147u,
			5153u,
			5167u,
			5171u,
			5179u,
			5189u,
			5197u,
			5209u,
			5227u,
			5231u,
			5233u,
			5237u,
			5261u,
			5273u,
			5279u,
			5281u,
			5297u,
			5303u,
			5309u,
			5323u,
			5333u,
			5347u,
			5351u,
			5381u,
			5387u,
			5393u,
			5399u,
			5407u,
			5413u,
			5417u,
			5419u,
			5431u,
			5437u,
			5441u,
			5443u,
			5449u,
			5471u,
			5477u,
			5479u,
			5483u,
			5501u,
			5503u,
			5507u,
			5519u,
			5521u,
			5527u,
			5531u,
			5557u,
			5563u,
			5569u,
			5573u,
			5581u,
			5591u,
			5623u,
			5639u,
			5641u,
			5647u,
			5651u,
			5653u,
			5657u,
			5659u,
			5669u,
			5683u,
			5689u,
			5693u,
			5701u,
			5711u,
			5717u,
			5737u,
			5741u,
			5743u,
			5749u,
			5779u,
			5783u,
			5791u,
			5801u,
			5807u,
			5813u,
			5821u,
			5827u,
			5839u,
			5843u,
			5849u,
			5851u,
			5857u,
			5861u,
			5867u,
			5869u,
			5879u,
			5881u,
			5897u,
			5903u,
			5923u,
			5927u,
			5939u,
			5953u,
			5981u,
			5987u
		};

		private static RandomNumberGenerator rng;

		private static RandomNumberGenerator Rng
		{
			get
			{
				if (rng == null)
				{
					rng = RandomNumberGenerator.Create();
				}
				return rng;
			}
		}

		public BigInteger()
		{
			this.data = new uint[20];
		}

		public BigInteger(Sign sign, uint len)
		{
			this.data = new uint[len];
			this.length = len;
		}

		public BigInteger(BigInteger bi)
		{
			this.data = (uint[])bi.data.Clone();
			this.length = bi.length;
		}

		public BigInteger(BigInteger bi, uint len)
		{
			this.data = new uint[len];
			for (uint num = 0u; num < bi.length; num++)
			{
				this.data[num] = bi.data[num];
			}
			this.length = bi.length;
		}

		public static BigInteger Parse(string number)
		{
			if (number == null)
			{
				throw new ArgumentNullException(number);
			}
			int i = 0;
			int num = number.Length;
			bool flag = false;
			BigInteger bigInteger = new BigInteger(0u);
			if (number[i] == '+')
			{
				i++;
			}
			else if (number[i] == '-')
			{
				throw new FormatException("Only positive integers are allowed.");
			}
			for (; i < num; i++)
			{
				char c = number[i];
				switch (c)
				{
				case '\0':
					i = num;
					continue;
				case '0':
				case '1':
				case '2':
				case '3':
				case '4':
				case '5':
				case '6':
				case '7':
				case '8':
				case '9':
					bigInteger = bigInteger * 10 + (c - 48);
					flag = true;
					continue;
				}
				if (char.IsWhiteSpace(c))
				{
					for (i++; i < num; i++)
					{
						if (!char.IsWhiteSpace(number[i]))
						{
							throw new FormatException();
						}
					}
					break;
				}
				throw new FormatException();
			}
			if (!flag)
			{
				throw new FormatException();
			}
			return bigInteger;
		}

		public BigInteger(byte[] inData)
		{
			this.length = (uint)inData.Length >> 2;
			int num = inData.Length & 3;
			if (num != 0)
			{
				this.length++;
			}
			this.data = new uint[this.length];
			int num2 = inData.Length - 1;
			int num3 = 0;
			while (num2 >= 3)
			{
				this.data[num3] = (uint)((inData[num2 - 3] << 24) | (inData[num2 - 2] << 16) | (inData[num2 - 1] << 8) | inData[num2]);
				num2 -= 4;
				num3++;
			}
			switch (num)
			{
			case 1:
				this.data[this.length - 1] = inData[0];
				break;
			case 2:
				this.data[this.length - 1] = (uint)((inData[0] << 8) | inData[1]);
				break;
			case 3:
				this.data[this.length - 1] = (uint)((inData[0] << 16) | (inData[1] << 8) | inData[2]);
				break;
			}
			Normalize();
		}

		public BigInteger(uint[] inData)
		{
			this.length = (uint)inData.Length;
			this.data = new uint[this.length];
			int num = (int)(this.length - 1);
			int num2 = 0;
			while (num >= 0)
			{
				this.data[num2] = inData[num];
				num--;
				num2++;
			}
			Normalize();
		}

		public BigInteger(uint ui)
		{
			this.data = new uint[1]
			{
				ui
			};
		}

		public BigInteger(ulong ul)
		{
			this.data = new uint[2]
			{
				(uint)ul,
				(uint)(ul >> 32)
			};
			this.length = 2u;
			Normalize();
		}

		public static implicit operator BigInteger(uint value)
		{
			return new BigInteger(value);
		}

		public static implicit operator BigInteger(int value)
		{
			if (value < 0)
			{
				throw new ArgumentOutOfRangeException(nameof(value));
			}
			return new BigInteger((uint)value);
		}

		public static implicit operator BigInteger(ulong value)
		{
			return new BigInteger(value);
		}

		public static BigInteger operator +(BigInteger bi1, BigInteger bi2)
		{
			if (bi1 == 0u)
			{
				return new BigInteger(bi2);
			}
			if (bi2 == 0u)
			{
				return new BigInteger(bi1);
			}
			return Kernel.AddSameSign(bi1, bi2);
		}

		public static BigInteger operator -(BigInteger bi1, BigInteger bi2)
		{
			if (bi2 == 0u)
			{
				return new BigInteger(bi1);
			}
			if (bi1 == 0u)
			{
				throw new ArithmeticException("Operation would return a negative value");
			}
			switch (Kernel.Compare(bi1, bi2))
			{
			case Sign.Zero:
				return 0;
			case Sign.Positive:
				return Kernel.Subtract(bi1, bi2);
			case Sign.Negative:
				throw new ArithmeticException("Operation would return a negative value");
			default:
				throw new Exception();
			}
		}

		public static int operator %(BigInteger bi, int i)
		{
			if (i > 0)
			{
				return (int)Kernel.DwordMod(bi, (uint)i);
			}
			return (int)(0 - Kernel.DwordMod(bi, (uint)(-i)));
		}

		public static uint operator %(BigInteger bi, uint ui)
		{
			return Kernel.DwordMod(bi, ui);
		}

		public static BigInteger operator %(BigInteger bi1, BigInteger bi2)
		{
			return Kernel.multiByteDivide(bi1, bi2)[1];
		}

		public static BigInteger operator /(BigInteger bi, int i)
		{
			if (i > 0)
			{
				return Kernel.DwordDiv(bi, (uint)i);
			}
			throw new ArithmeticException("Operation would return a negative value");
		}

		public static BigInteger operator /(BigInteger bi1, BigInteger bi2)
		{
			return Kernel.multiByteDivide(bi1, bi2)[0];
		}

		public static BigInteger operator *(BigInteger bi1, BigInteger bi2)
		{
			if (bi1 == 0u || bi2 == 0u)
			{
				return 0;
			}
			if (bi1.data.Length < bi1.length)
			{
				throw new IndexOutOfRangeException("bi1 out of range");
			}
			if (bi2.data.Length < bi2.length)
			{
				throw new IndexOutOfRangeException("bi2 out of range");
			}
			BigInteger bigInteger = new BigInteger(Sign.Positive, bi1.length + bi2.length);
			Kernel.Multiply(bi1.data, 0u, bi1.length, bi2.data, 0u, bi2.length, bigInteger.data, 0u);
			bigInteger.Normalize();
			return bigInteger;
		}

		public static BigInteger operator *(BigInteger bi, int i)
		{
			if (i < 0)
			{
				throw new ArithmeticException("Operation would return a negative value");
			}
			switch (i)
			{
			case 0:
				return 0;
			case 1:
				return new BigInteger(bi);
			default:
				return Kernel.MultiplyByDword(bi, (uint)i);
			}
		}

		public static BigInteger operator <<(BigInteger bi1, int shiftVal)
		{
			return Kernel.LeftShift(bi1, shiftVal);
		}

		public static BigInteger operator >>(BigInteger bi1, int shiftVal)
		{
			return Kernel.RightShift(bi1, shiftVal);
		}

		public static BigInteger genRandom(int bits, RandomNumberGenerator rng)
		{
			int num = bits >> 5;
			int num2 = bits & 0x1F;
			if (num2 != 0)
			{
				num++;
			}
			BigInteger bigInteger = new BigInteger(Sign.Positive, (uint)(num + 1));
			byte[] src = new byte[num << 2];
			rng.GetBytes(src);
			Buffer.BlockCopy(src, 0, bigInteger.data, 0, num << 2);
			if (num2 != 0)
			{
				uint num3 = (uint)(1 << num2 - 1);
				uint[] array;
				uint[] array2 = array = bigInteger.data;
				int num4 = num - 1;
				IntPtr intPtr = (IntPtr)num4;
				array2[num4] = (array[(long)intPtr] | num3);
				num3 = uint.MaxValue >> 32 - num2;
				uint[] array3 = array = bigInteger.data;
				int num5 = num - 1;
				intPtr = (IntPtr)num5;
				array3[num5] = (array[(long)intPtr] & num3);
			}
			else
			{
				uint[] array;
				uint[] array4 = array = bigInteger.data;
				int num6 = num - 1;
				IntPtr intPtr = (IntPtr)num6;
				array4[num6] = (uint)((int)array[(long)intPtr] | int.MinValue);
			}
			bigInteger.Normalize();
			return bigInteger;
		}

		public static BigInteger genRandom(int bits)
		{
			return genRandom(bits, Rng);
		}

		public void randomize(RandomNumberGenerator rng)
		{
			int num = bitCount();
			int num2 = num >> 5;
			int num3 = num & 0x1F;
			if (num3 != 0)
			{
				num2++;
			}
			byte[] src = new byte[num2 << 2];
			rng.GetBytes(src);
			Buffer.BlockCopy(src, 0, this.data, 0, num2 << 2);
			if (num3 != 0)
			{
				uint num4 = (uint)(1 << num3 - 1);
				uint[] array;
				uint[] array2 = array = this.data;
				int num5 = num2 - 1;
				IntPtr intPtr = (IntPtr)num5;
				array2[num5] = (array[(long)intPtr] | num4);
				num4 = uint.MaxValue >> 32 - num3;
				uint[] array3 = array = this.data;
				int num6 = num2 - 1;
				intPtr = (IntPtr)num6;
				array3[num6] = (array[(long)intPtr] & num4);
			}
			else
			{
				uint[] array;
				uint[] array4 = array = this.data;
				int num7 = num2 - 1;
				IntPtr intPtr = (IntPtr)num7;
				array4[num7] = (uint)((int)array[(long)intPtr] | int.MinValue);
			}
			Normalize();
		}

		public void randomize()
		{
			randomize(Rng);
		}

		public int bitCount()
		{
			Normalize();
			uint num = this.data[this.length - 1];
			uint num2 = 2147483648u;
			uint num3 = 32u;
			while (num3 != 0 && (num & num2) == 0)
			{
				num3--;
				num2 >>= 1;
			}
			return (int)(num3 + (this.length - 1 << 5));
		}

		public bool testBit(uint bitNum)
		{
			uint num = bitNum >> 5;
			byte b = (byte)(bitNum & 0x1F);
			uint num2 = (uint)(1 << (int)b);
			return (this.data[num] & num2) != 0;
		}

		public bool testBit(int bitNum)
		{
			if (bitNum < 0)
			{
				throw new IndexOutOfRangeException("bitNum out of range");
			}
			uint num = (uint)bitNum >> 5;
			byte b = (byte)(bitNum & 0x1F);
			uint num2 = (uint)(1 << (int)b);
			return (this.data[num] | num2) == this.data[num];
		}

		public void setBit(uint bitNum)
		{
			setBit(bitNum, val: true);
		}

		public void clearBit(uint bitNum)
		{
			setBit(bitNum, val: false);
		}

		public unsafe void setBit(uint bitNum, bool val)
		{
			uint num = bitNum >> 5;
			if (num < this.length)
			{
				uint num2 = (uint)(1 << (int)(bitNum & 0x1F));
				if (val)
				{
					uint[] array;
					IntPtr intPtr;
					(array = this.data)[(long)(intPtr = (IntPtr)(void*)num)] = (array[(long)intPtr] | num2);
				}
				else
				{
					uint[] array;
					IntPtr intPtr;
					(array = this.data)[(long)(intPtr = (IntPtr)(void*)num)] = (array[(long)intPtr] & ~num2);
				}
			}
		}

		public int LowestSetBit()
		{
			if (this == 0u)
			{
				return -1;
			}
			int i;
			for (i = 0; !testBit(i); i++)
			{
			}
			return i;
		}

		public byte[] getBytes()
		{
			if (this == 0u)
			{
				return new byte[1];
			}
			int num = bitCount();
			int num2 = num >> 3;
			if ((num & 7) != 0)
			{
				num2++;
			}
			byte[] array = new byte[num2];
			int num3 = num2 & 3;
			if (num3 == 0)
			{
				num3 = 4;
			}
			int num4 = 0;
			for (int num5 = (int)(this.length - 1); num5 >= 0; num5--)
			{
				uint num6 = this.data[num5];
				for (int num7 = num3 - 1; num7 >= 0; num7--)
				{
					array[num4 + num7] = (byte)(num6 & 0xFF);
					num6 >>= 8;
				}
				num4 += num3;
				num3 = 4;
			}
			return array;
		}

		public static bool operator ==(BigInteger bi1, uint ui)
		{
			if (bi1.length != 1)
			{
				bi1.Normalize();
			}
			if (bi1.length == 1)
			{
				return bi1.data[0] == ui;
			}
			return false;
		}

		public static bool operator !=(BigInteger bi1, uint ui)
		{
			if (bi1.length != 1)
			{
				bi1.Normalize();
			}
			if (bi1.length == 1)
			{
				return bi1.data[0] != ui;
			}
			return true;
		}

		public static bool operator ==(BigInteger bi1, BigInteger bi2)
		{
			if ((object)bi1 == bi2)
			{
				return true;
			}
			if (null == bi1 || null == bi2)
			{
				return false;
			}
			return Kernel.Compare(bi1, bi2) == Sign.Zero;
		}

		public static bool operator !=(BigInteger bi1, BigInteger bi2)
		{
			if ((object)bi1 == bi2)
			{
				return false;
			}
			if (null == bi1 || null == bi2)
			{
				return true;
			}
			return Kernel.Compare(bi1, bi2) != Sign.Zero;
		}

		public static bool operator >(BigInteger bi1, BigInteger bi2)
		{
			return Kernel.Compare(bi1, bi2) > Sign.Zero;
		}

		public static bool operator <(BigInteger bi1, BigInteger bi2)
		{
			return Kernel.Compare(bi1, bi2) < Sign.Zero;
		}

		public static bool operator >=(BigInteger bi1, BigInteger bi2)
		{
			return Kernel.Compare(bi1, bi2) >= Sign.Zero;
		}

		public static bool operator <=(BigInteger bi1, BigInteger bi2)
		{
			return Kernel.Compare(bi1, bi2) <= Sign.Zero;
		}

		public Sign Compare(BigInteger bi)
		{
			return Kernel.Compare(this, bi);
		}

		public string ToString(uint radix)
		{
			return ToString(radix, "0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZ");
		}

		public string ToString(uint radix, string charSet)
		{
			if (charSet.Length < radix)
			{
				throw new ArgumentException("charSet length less than radix", "charSet");
			}
			if (radix == 1)
			{
				throw new ArgumentException("There is no such thing as radix one notation", "radix");
			}
			if (this == 0u)
			{
				return "0";
			}
			if (this == 1u)
			{
				return "1";
			}
			string text = "";
			BigInteger bigInteger = new BigInteger(this);
			while (bigInteger != 0u)
			{
				uint index = Kernel.SingleByteDivideInPlace(bigInteger, radix);
				text = charSet[(int)index] + text;
			}
			return text;
		}

		private void Normalize()
		{
			while (this.length != 0 && this.data[this.length - 1] == 0)
			{
				this.length--;
			}
			if (this.length == 0)
			{
				this.length++;
			}
		}

		public void Clear()
		{
			for (int i = 0; i < this.length; i++)
			{
				this.data[i] = 0u;
			}
		}

		public override int GetHashCode()
		{
			uint num = 0u;
			for (uint num2 = 0u; num2 < this.length; num2++)
			{
				num ^= this.data[num2];
			}
			return (int)num;
		}

		public override string ToString()
		{
			return ToString(10u);
		}

		public override bool Equals(object o)
		{
			if (o == null)
			{
				return false;
			}
			if (o is int)
			{
				if ((int)o >= 0)
				{
					return this == (uint)o;
				}
				return false;
			}
			return Kernel.Compare(this, (BigInteger)o) == Sign.Zero;
		}

		public BigInteger gcd(BigInteger bi)
		{
			return Kernel.gcd(this, bi);
		}

		public BigInteger modInverse(BigInteger mod)
		{
			return Kernel.modInverse(this, mod);
		}

		public BigInteger modPow(BigInteger exp, BigInteger n)
		{
			ModulusRing modulusRing = new ModulusRing(n);
			return modulusRing.Pow(this, exp);
		}

		public bool isProbablePrime()
		{
			for (int i = 0; i < smallPrimes.Length; i++)
			{
				if (this == smallPrimes[i])
				{
					return true;
				}
				if (this % smallPrimes[i] == 0)
				{
					return false;
				}
			}
			return PrimalityTests.RabinMillerTest(this, ConfidenceFactor.Medium);
		}

		[Obsolete]
		public bool isProbablePrime(int notUsed)
		{
			for (int i = 0; i < smallPrimes.Length; i++)
			{
				if (this % smallPrimes[i] == 0)
				{
					return false;
				}
			}
			return PrimalityTests.SmallPrimeSppTest(this, ConfidenceFactor.Medium);
		}

		public static BigInteger NextHightestPrime(BigInteger bi)
		{
			NextPrimeFinder nextPrimeFinder = new NextPrimeFinder();
			return nextPrimeFinder.GenerateNewPrime(0, bi);
		}

		public static BigInteger genPseudoPrime(int bits)
		{
			SequentialSearchPrimeGeneratorBase sequentialSearchPrimeGeneratorBase = new SequentialSearchPrimeGeneratorBase();
			return sequentialSearchPrimeGeneratorBase.GenerateNewPrime(bits);
		}

		public void Incr2()
		{
			int num = 0;
			uint[] array;
			(array = this.data)[0] = array[0] + 2;
			if (this.data[0] < 2)
			{
				uint[] array2 = array = this.data;
				int num2 = ++num;
				IntPtr intPtr = (IntPtr)num2;
				array2[num2] = array[(long)intPtr] + 1;
				while (this.data[num++] == 0)
				{
					uint[] array3 = array = this.data;
					int num3 = num;
					intPtr = (IntPtr)num3;
					array3[num3] = array[(long)intPtr] + 1;
				}
				if (this.length == (uint)num)
				{
					this.length++;
				}
			}
		}
	}
}
