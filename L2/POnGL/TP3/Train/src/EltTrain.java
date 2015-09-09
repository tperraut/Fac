
abstract public class EltTrain
{
	/**
	 *  Un élément de train possède un nom et un poids, et ces derniers ne
	 *  changent pas.
	 */
	protected final String	nom;
	protected final int		poids;
	
	/**
	 * À la création d'un élément de train, on lui affecte un poids (fourni
	 * en argument) et un nom. Le nom est généré automatiquement, et il doit
	 * être unique.
	 * @param poids  indique le poids de l'élément.
	 */
	public EltTrain(int poids)
	{
		nom = null;
		this.poids = poids;
	}
	
	/**
	 * Renvoie le poids total d'un élément de train. Pour les éléments
	 * transportant des passagers ou des marchandises, cette mèthode devra
	 * être redéfinie.
	 * @return  le poids de l'élément.
	 */
	public int getPoids()
	{
		return poids;
	}
	
}
