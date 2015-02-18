
public class Locomotive extends EltTrain implements EltMoteur
{
	/**
	 * Attribut indiquant la capacité de traction maximale.
	 */
	private int tractionMax;
	
	/**
	 * Constructeur de Locomotive
	 * @param poids  donne le poids de l'élément
	 * @param tractionMax  donne sa capacité de traction maximale.
	 */
	public Locomotive(int poids, int tractionMax)
	{
		super(poids);
		this.tractionMax = tractionMax;
	}

	/**
	 * Renvoie la capacité de traction maximale.
	 */
	@Override
	public int getTractionMax()
	{
		return (tractionMax);
	}

}
