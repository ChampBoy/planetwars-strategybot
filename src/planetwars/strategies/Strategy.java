/*
Written By :
Agnes Folga : folga003@umn.edu
Sunny Parawala : paraw001@umn.edu
 */
package planetwars.strategies;
//Import Statements
import org.jgrapht.*;
import org.jgrapht.graph.DefaultEdge;
import org.jgrapht.graph.SimpleWeightedGraph;
import planetwars.publicapi.*;
import org.jgrapht.alg.shortestpath.DijkstraShortestPath;

import java.util.*;

public class Strategy implements IStrategy {
    /**
     * This inner class compares two planets based on number of edges and habitability, implements comparator
     */
    public class ComparePlanets implements Comparator<IVisiblePlanet> {
        /**
         * @param planet1 planet number 1 to be compared
         * @param planet2 planet number 2 to be compared
         * @return  returns -1 if planet 1 should be prioritized otherwise returns 1
         */
        public int compare(IVisiblePlanet planet1, IVisiblePlanet planet2) {
            int planet1growth = planet1.getHabitability();
            int planet2growth = planet2.getHabitability();
            int planet1edges = planet1.getEdges().size();
            int planet2edges = planet2.getEdges().size();

            if (planet1edges >= planet2edges * 2) {
                return -1;
            } else if (planet1edges >= planet2edges) {
                if (planet1growth >= planet2growth) {
                    return -1;
                }
                if (planet1growth * 2 <= planet2growth) {
                    return 1;
                } else {
                    return -1;
                }
            } else {
                return 1;
            }
        }
    }

    /**
     * This inner class keeps track of events to be executed in the future
     */
    public class FutureTurns
    {
        private IPlanet source;
        private IPlanet sink;
        private long population;
        private double correctturn ;

        /**
         *
         * @param source Planet to attack from
         * @param sink   Planet to attack
         * @param population    Population to attack with
         * @param correctturn   Correct turn to execute the action
         */
        public FutureTurns(IPlanet source, IPlanet sink, long population, double correctturn)
        {
            this.source= source;
            this.sink=sink;
            this.population= population;
            this.correctturn= correctturn;
        }
        public IPlanet getSource()
        {
            return this.source;
        }
        public IPlanet getSink()
        {
            return this.sink ;
        }
        public long getPopulation()
        {
            return this.population;
        }
        public double getCorrectturn()
        {
            return this.correctturn;
        }
    }

    /**
     * planetID : Hashmap with key as planet id and value as Planet
     * conquered and unconquered visible planets are lists containing Id's of planets which are visible and conquered/unconquered
     * unc_pplt is a priority queue of unconquered planets
     * my_pplt is a priority queue of conquered planets
     * frontline planet is a planet which is connected to atleast one neutral or enemy planet
     * frontline and non frontline are two Integer lists which store the ID's accordingly
     * future is a list of "FutureTurns"
     */
    private Graph<IPlanet, DefaultEdge> graph;
    private boolean firstTurn = true;
    private int num_planets;
    private Random random;
    private HashMap<Integer, IPlanet> planetID;
    private List<Integer> conqueredVisiblePlanets;
    private List<Integer> unconqueredVisiblePlanets;
    private PriorityQueue<IVisiblePlanet> unc_pplt;
    private PriorityQueue<IVisiblePlanet> my_pplt;
    private DijkstraShortestPath<IPlanet,DefaultEdge> dp;
    private List<Integer> frontline;
    private List<Integer> nonfrontline;
    private int turn_counter=0;
    private List<FutureTurns> future ;
    public Strategy() {
        random = new Random();
        graph = new SimpleWeightedGraph<IPlanet, DefaultEdge>(DefaultEdge.class);
        dp= new DijkstraShortestPath<>(graph);
        future= new ArrayList<>();

    }

    /**
     * Method stimualtes all turns in the game
     * @param planets          The current state of the system.
     * @param planetOperations Helper methods students can use to interact with the system.
     * @param eventsToExecute  Queue students will add to in order to schedule events.
     */
    public void takeTurn(List<IPlanet> planets, IPlanetOperations planetOperations, Queue<IEvent> eventsToExecute)
    {
        if (firstTurn) {
            num_planets = planets.size();
            firstTurn = false;
        }
        planetID = new HashMap<>();
        for (IPlanet planet : planets) {
            planetID.putIfAbsent(planet.getId(), planet);
        }
        this.makeGraph(planets);
        this.updatePlanetMap(planets);
        this.updateFrontLine(planets);
        this.updatePriorityQueues();
        // This for loop executes future turns if its the correct turn number
        for(FutureTurns turn : future)
        {
            if(turn.getCorrectturn()==turn_counter)
            {
                IPlanet source = turn.getSource();
                IPlanet sink = turn.getSink();
                long pop = turn.getPopulation();
                eventsToExecute.offer(planetOperations.transferPeople(source, sink, pop));
                future.remove(turn);
            }
        }
        // This for loop sends help to frontline planets if non frontline planet has a big population
        for(IPlanet planet : planets)
        {
            //Checking if planet is eligible to send help
            if (conqueredVisiblePlanets.contains(planet.getId()) && ((IVisiblePlanet)planet).getPopulation()>150 && nonfrontline.contains(planet.getId()))
            {
                //Finds a random frontline planet to send help to
                int send_here_id= frontline.get(random.nextInt(frontline.size()));
                IPlanet send_here = planetID.get(send_here_id);
                if(send_here!=null)
                {
                    if(graph.containsEdge(planet,send_here))
                    {
                        eventsToExecute.offer(planetOperations.transferPeople(planet, send_here, 110));
                    }
                    else {

                        GraphPath<IPlanet, DefaultEdge> dj = dp.getPath(planet, send_here);
                        List<IPlanet> vertices = dj.getVertexList();
                        Iterator<IPlanet> itr = vertices.iterator();
                        IPlanet tempplanet = itr.next();
                        long to_send = ((IVisiblePlanet) tempplanet).getPopulation() / 2;
                        IPlanet next = itr.next();
                        double app_turn = turn_counter + graph.getEdgeWeight(graph.getEdge(tempplanet, next));
                        eventsToExecute.offer(planetOperations.transferPeople(tempplanet, next, to_send));
                        while (itr.hasNext()) {
                            tempplanet = next;
                            next = itr.next();
                            FutureTurns newturn = new FutureTurns(tempplanet, next, to_send, app_turn);
                            future.add(newturn);
                            app_turn += graph.getEdgeWeight(graph.getEdge(tempplanet, next));
                        }
                    }
                }
            }
        }
        // Finds neutral planets and sends ships to conquer them
        IVisiblePlanet planet_to_attack = null;
        PriorityQueue<IVisiblePlanet> unc_copy = new PriorityQueue<>(unc_pplt);
        while (!unc_copy.isEmpty()) {
            planet_to_attack = unc_copy.poll();
            if (planet_to_attack.getOwner() == Owner.NEUTRAL) {
                IVisiblePlanet planet = findClosestMyPlanet(planet_to_attack);
                Set<IEdge> edges = planet_to_attack.getEdges();
                Iterator<IEdge> itr = edges.iterator();
                while(itr.hasNext()){
                    IEdge next_edge = itr.next();
                    if (conqueredVisiblePlanets.contains(next_edge.getDestinationPlanetId())) {
                        IPlanet planet_from = planetID.get(next_edge.getDestinationPlanetId());
                        if ((((IVisiblePlanet) planet_from).getPopulation() > 2)) {
                            eventsToExecute.offer(planetOperations.transferPeople(planet_from, planet_to_attack, ((IVisiblePlanet) planet_from).getPopulation() / 3));
                        }

                    }
                }
            }
        }
        // Following code sends help from non frontline planets to frontline planets
        List<IPlanet> used_backlines = new ArrayList<>();
        for ( Integer planet_to_help : frontline)
        {
            IPlanet random_myplanet = null ;
            for( Integer i : nonfrontline)
            {
                if( ((IVisiblePlanet)planetID.get(i)).getPopulation()>15 && !(used_backlines.contains(planetID.get(i))))
                {
                    random_myplanet = planetID.get(i);
                    GraphPath<IPlanet, DefaultEdge> dj = dp.getPath(random_myplanet, planetID.get(planet_to_help));
                    List<IPlanet> vertices = dj.getVertexList();
                    Iterator<IPlanet> itr = vertices.iterator();
                    IPlanet tempplanet = itr.next();
                    used_backlines.add(tempplanet);
                    long to_send = ((IVisiblePlanet)tempplanet).getPopulation()/2;
                    IPlanet next = itr.next();
                    double app_turn= turn_counter + graph.getEdgeWeight(graph.getEdge(tempplanet,next));
                    eventsToExecute.offer(planetOperations.transferPeople(tempplanet,next,to_send));
                    while (itr.hasNext())
                    {
                        tempplanet=next;
                        next = itr.next();
                        FutureTurns newturn = new FutureTurns(tempplanet, next,to_send, app_turn);
                        future.add(newturn);
                        app_turn+= graph.getEdgeWeight(graph.getEdge(tempplanet, next));
                    }
                    break;
                }
            }
        }
        // attack closest enemy while looping through all frontline planets
        for (Integer to_attack_from : frontline ) {
            IPlanet planet_to_attack_from = planetID.get(to_attack_from);
            if (((IVisiblePlanet) planet_to_attack_from).getPopulation() >= 5) {
                IVisiblePlanet attack_me = findClosestEnemyPlanet((IVisiblePlanet) planet_to_attack_from);
                double pop_to_defeat = attack_me.getPopulation()*1.1 + attack_me.getHabitability();
                if(((IVisiblePlanet) planet_to_attack_from).getPopulation() >pop_to_defeat) {
                    eventsToExecute.offer(planetOperations.transferPeople(planet_to_attack_from, attack_me, (long)pop_to_defeat + 5));
                }
            }
        }
        turn_counter++;
    }

    /**
     * the updateFrontLine method finds frontline planets and adds to the frontline planet list, and does the same for nonfrontline planets
     * @param planets: takes in a list of planets to see which ones are frontline or nonfrontline
     */
    public void updateFrontLine(List <IPlanet> planets)
    {
        nonfrontline = new ArrayList<Integer>(num_planets);
        frontline = new ArrayList<Integer>(num_planets);
        for( IPlanet planet : planets )
        {
            boolean is_frontline= false;
            Set<IEdge> edges = planet.getEdges();
            for(IEdge edge : edges)
            {
                if(unconqueredVisiblePlanets.contains(edge.getDestinationPlanetId()))
                {
                    if(!frontline.contains(planet.getId()) && conqueredVisiblePlanets.contains(planet.getId()))
                    {
                        frontline.add(planet.getId());
                        is_frontline=true;
                    }
                }
            }
            if(!is_frontline)
            {
                if(conqueredVisiblePlanets.contains(planet.getId()))
                {
                    nonfrontline.add(planet.getId());
                }
            }
        }
    }

    /**
     * this method finds which planets have priority based off the number of edges a planet has and secondly off its habitability rates
     */
    public void updatePriorityQueues()
    {
        unc_pplt = new PriorityQueue<IVisiblePlanet>(num_planets, new ComparePlanets());
        my_pplt = new PriorityQueue<IVisiblePlanet>(num_planets, new ComparePlanets());
        for (Integer planet_id : unconqueredVisiblePlanets) {
            unc_pplt.add((IVisiblePlanet)planetID.get(planet_id));
        }
        for (Integer planet_id : conqueredVisiblePlanets) {
            my_pplt.add((IVisiblePlanet)planetID.get(planet_id));
        }
    }

    /**
     * this method finds the closest myplanet based off of edges
     * @param planet: planet to find the closest myplanet to
     * @return : closest planet
     */

    public IVisiblePlanet findClosestMyPlanet (IVisiblePlanet planet)
    {
        IPlanet temp = null;
        Set<IEdge> edges = planet.getEdges();
        double shortest_length = 99999;
        for (IEdge edge : edges) {
            Integer destination_planet_id = edge.getDestinationPlanetId();
            IPlanet destination_planet= planetID.get(destination_planet_id);
            if (destination_planet instanceof IVisiblePlanet && conqueredVisiblePlanets.contains(destination_planet.getId())) {
                if (edge.getLength() < shortest_length) {
                    shortest_length = edge.getLength();
                    temp = destination_planet;
                }
            }
        }
        return ((IVisiblePlanet) temp);
    }

    /**
     * This method finds the closest enemy planet
     * @param planet the planet we need to find the closest enemy to
     * @return An IVisible planet which is the closest enemy
     */
    public IVisiblePlanet findClosestEnemyPlanet (IVisiblePlanet planet)
    {
        IPlanet temp = null;
        Set<IEdge> edges = planet.getEdges();
        double shortest_length = 99999;
        for (IEdge edge : edges) {
            Integer destination_planet_id = edge.getDestinationPlanetId();
            IPlanet destination_planet= planetID.get(destination_planet_id);
            if (destination_planet instanceof IVisiblePlanet && unconqueredVisiblePlanets.contains(destination_planet.getId()) && ((IVisiblePlanet) destination_planet).getOwner()==Owner.OPPONENT) {
                if (edge.getLength() < shortest_length) {
                    shortest_length = edge.getLength();
                    temp = destination_planet;
                }
            }
        }
        return ((IVisiblePlanet) temp);
    }

    /**
     * this method updates the planet map by adding planets to the unconquered and the conquered planets
     * @param planets : A list of planets
     */
    public void updatePlanetMap (List < IPlanet > planets)
    {
        conqueredVisiblePlanets = new ArrayList<>();
        unconqueredVisiblePlanets = new ArrayList<>();
        for (IPlanet planet : planets) {
            if (planet instanceof IVisiblePlanet && ((IVisiblePlanet) planet).getOwner() == Owner.SELF) {
                conqueredVisiblePlanets.add(planet.getId());
            } else if (planet instanceof IVisiblePlanet) {
                unconqueredVisiblePlanets.add(planet.getId());
            }
        }
    }

    /**
     *  This Method makes a graph
     * @param planets : list of planets
     */
    public void makeGraph (List < IPlanet > planets)
    {
        for (IPlanet planet : planets) {
            graph.addVertex(planet);
        }
        for (IPlanet planet : planets) {
            Set<IEdge> edges = planet.getEdges();
            for (IEdge edge : edges) {
                if (!graph.containsEdge(planet, planetID.get(edge.getDestinationPlanetId()))) {
                    graph.addEdge(planet, planetID.get(edge.getDestinationPlanetId()));
                    graph.setEdgeWeight(planet, planetID.get(edge.getDestinationPlanetId()), edge.getLength());
                }
            }
        }
    }
    public String getName () {
        return "Chads__Lads";
    }
    public boolean compete () {
        return true;
    }
}