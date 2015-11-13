public class ThreadML extends Thread
{
	private Matrice mA;
	private Matrice mB;
	private Matrice mRES;
	private int li;
	private int co;

	public ThreadML(Matrice matA, Matrice matB, Matrice mRES, int li)
	{
		this.mA = matA;
		this.mB = matB;
		this.mRES = mRES;
		this.li = li;
		this.co = matB.getLine();
	}

	@Override
	public void run()
	{
		for (int j = 0; j < this.co; j++)
		{
			MMperLine.setVtoRes(mRES, multTable(this.mA.getLi(li),
						this.mB.getLi(j)), this.li, j);
		}
	}
	private int multTable(int l1[], int l2[])
	{
		int result = 0;

		for (int i = 0; i < l1.length; i++)
			result += l1[i] * l2[i];
		return result;
	}
}
