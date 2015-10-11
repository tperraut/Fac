public class ThreadM extends Thread
{
	private Matrice mA;
	private Matrice mB;
	private Matrice mRES;
	private int li;
	private int co;

	public ThreadM(Matrice matA, Matrice matB, Matrice mRES, int li, int co)
	{
		this.mA = matA;
		this.mB = matB;
		this.mRES = mRES;
		this.li = li;
		this.co = co;
	}

	@Override
	public void run()
	{
		MMperVal.setVtoRes(mRES, multTable(this.mA.getLi(li),
						this.mB.getLi(co)),
					this.li, this.co);
	}
	private int multTable(int l1[], int l2[])
	{
		int result = 0;

		for (int i = 0; i < l1.length; i++)
			result += l1[i] * l2[i];
		return result;
	}
}
