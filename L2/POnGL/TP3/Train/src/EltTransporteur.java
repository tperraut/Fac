import java.util.ArrayList;

/**
 * Une classe pour les éléments de train pouvant avoir un chargement.
 * @param <T>  désigne le type de chargement, à choisir parmi les classes
 * qui héritent de [Transportable].
 */
abstract public class EltTransporteur<T extends Transportable> extends EltTrain implements Transporteur<T>
{
	/**
	 * Capacité de l'élément transporteur, et liste des choses transporées.
	 * Selon les cas, la capacité désignera un nombre d'élément ou un
	 * volume.
	 */
	protected final int capacite;
	protected ArrayList<T> cargo;
	/**
	 * Constructeur standard pour un élément transporteur, qui ne
	 * transporte rien à l'origine.
	 * @param poids     désigne le poids à vide de l'élément
	 * @param capacite  désigne la capacité de transport de l'élément
	 */
	public EltTransporteur(int poids, int capacite){
		super(poids);
		this.capacite = capacite;
		cargo = new ArrayList<T>();
	}
	
	/**
	 * Calcul du poids des choses transportées.
	 * @return  le poids total des choses transportées.
	 */
	public int poidsDesTransportables()
	{
		int	poidsDT = 0;
		for (T t : this.cargo)
			poidsDT += t.getPoids();
		return (poidsDT);
	}
	
	/**
	 * Calcul du poids total de l'élément transporteur, chargement
	 * inclusnstanceof A or B.
	 * @return  poids élément + choses transportées.
	 */
	@Override
	public int getPoids()
	{
		return (this.poids + this.poidsDesTransportables());
	}
	
	/**
	 * Tentative d'ajout d'un élément au chargement de l'élément.
	 * @param t  l'objet transportable à ajouter au chargement.
	 * @return  true si l'ajout a eu lieu, et false sinon.
	 */
	public boolean ajouterTransportable(T t)
	{
		if (this.poidsDesTransportables() + t.getPoids()
				< this.capacite * t.getPoids())
		{
			this.cargo.add(t);
			return (true);
		}
		return (false);
	}
	/**
	 * Creation d'un descriptif du chargement de l'élément.
	 * @return  le descriptif sous forme de chaîne de caractères.
	 */
	public String cargoToString(){
		String s = "";
		for(T t : cargo)
			s = s.concat(t.toString()) + " ";
		return s;
	}
	public int getCapacite()
	{
		return (this.capacite);
	}
}
