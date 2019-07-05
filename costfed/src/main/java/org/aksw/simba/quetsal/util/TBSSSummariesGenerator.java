package org.aksw.simba.quetsal.util;

import java.io.BufferedWriter;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.OutputStreamWriter;
import java.net.URI;
import java.net.URISyntaxException;
import java.net.URL;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.SortedSet;
import java.util.TreeSet;
import java.util.concurrent.Callable;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.Future;
import java.util.concurrent.atomic.AtomicInteger;

import org.aksw.simba.quetsal.datastructues.Trie;
import org.aksw.simba.quetsal.datastructues.Trie2;
import org.aksw.simba.quetsal.datastructues.TrieNode;
import org.aksw.simba.quetsal.datastructues.Tuple3;
import org.aksw.simba.quetsal.datastructues.Tuple4;
import org.aksw.simba.quetsal.synopsis.ArrayCollection;
import org.aksw.simba.quetsal.synopsis.Collection;
import org.aksw.simba.quetsal.synopsis.MIPsynopsis;
import org.apache.http.client.HttpClient;
import org.apache.http.impl.client.HttpClientBuilder;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import com.fluidops.fedx.structures.Pair;

import org.eclipse.rdf4j.http.client.util.HttpClientBuilders;
import org.eclipse.rdf4j.model.IRI;
import org.eclipse.rdf4j.model.Value;
import org.eclipse.rdf4j.query.BindingSet;
import org.eclipse.rdf4j.query.MalformedQueryException;
import org.eclipse.rdf4j.query.QueryEvaluationException;
import org.eclipse.rdf4j.query.QueryLanguage;
import org.eclipse.rdf4j.query.TupleQuery;
import org.eclipse.rdf4j.query.TupleQueryResult;
import org.eclipse.rdf4j.repository.RepositoryConnection;
import org.eclipse.rdf4j.repository.RepositoryException;
import org.eclipse.rdf4j.repository.sparql.SPARQLRepository;


/**
 *  Generate Quetzal-TBSS Summaries for a set of federation members (SPARQL endpoints)
 *  @author saleem
 */
public class TBSSSummariesGenerator {
	static Logger log = LoggerFactory.getLogger(TBSSSummariesGenerator.class);
	static {
		try {
			ClassLoader.getSystemClassLoader().loadClass("org.slf4j.LoggerFactory"). getMethod("getLogger", ClassLoader.getSystemClassLoader().loadClass("java.lang.String")).
			 invoke(null,"ROOT");
		} catch (Throwable e) {
			e.printStackTrace();
		}
	}
	
	public static HttpClientBuilder httpClientBuilder;
	public static HttpClient httpClient;
	
	static {
		httpClientBuilder = HttpClientBuilders.getSSLTrustAllHttpClientBuilder();
		httpClientBuilder.setMaxConnTotal(10);
		httpClientBuilder.setMaxConnPerRoute(5);
		//httpClientBuilder.setConnectionReuseStrategy(new NoConnectionReuseStrategy());
		httpClient = httpClientBuilder.build();
	}
	
	static Map<String, SPARQLRepository> reps = new HashMap<String, SPARQLRepository>();
	static SPARQLRepository createSPARQLRepository(String url) {
		SPARQLRepository repo = reps.get(url);
		if (repo == null) {
			repo = new SPARQLRepository(url);
			repo.setHttpClient(httpClient);
			repo.initialize();
			reps.put(url, repo);
		}
		return repo;
	}
	
	
	public BufferedWriter bwr;
	
	/**
	 * initialize input information for data summaries generation
	 * @param location Directory location of the resulting FedSummaries file (i.e. location/FedSum.n3)
	 * @throws IOException IO Exceptions
	 */
	public TBSSSummariesGenerator(String location) throws IOException 
	{
		bwr = new BufferedWriter(new OutputStreamWriter(new FileOutputStream(location), "UTF-8")); //--name/location where the summaries file will be stored
		bwr.append("@prefix ds:<http://aksw.org/quetsal/> .");
		bwr.newLine();
	}
	
	static boolean verifyIRI(Value obj) {
		if (!(obj instanceof IRI)) return false;
		return verifyIRI(obj.stringValue());
	}
	
	static boolean verifyIRI(String sval) {
		try {
			// exclude virtuoso specific data
			if (sval.startsWith("http://www.openlinksw.com/schemas") || sval.startsWith("http://www.openlinksw.com/virtrd")) return false;
			URL url = new URL(sval);
			new URI(url.getProtocol(), url.getAuthority(), url.getPath(), url.getQuery(), url.getRef()).toURL().toString();
			return url.getProtocol() != null && url.getAuthority() != null && !url.getAuthority().isEmpty();
		} catch (Exception e) {
			//log.warn("skip IRI: " + sval + ", error: " + e.getMessage());
			return false;
		}
	}
	
	static Pair<String, String> splitIRI(String iri) {
		String[] objPrts = iri.split("/");
		String objAuth = objPrts[0] + "//" + objPrts[2];
		return new Pair<String, String>(objAuth, iri.substring(objAuth.length()));
	}
	
	boolean putIRI(String iri, long hits, Trie2.Node nd) {
		Pair<String, String> pair = splitIRI(iri);
		return Trie2.insertWord(nd, pair.getFirst(), pair.getSecond(), hits);
	}
	
	static String makeWellFormed(String uri) {
		try {
			URL url = new URL(uri);
			return new URI(url.getProtocol(), url.getAuthority(), url.getPath(), url.getQuery(), url.getRef()).toURL().toString();
		} catch (Exception e) {
			log.error("Error in " + uri);
			throw new RuntimeException(e);
		}
	}
	
	static String encodeStringLiteral(String s) {
		if (s.indexOf((int)'"') == -1) {
			return s;
		}
		return s.replace("\"", "\\\"");
	}
	
	static int MIN_TOP_OBJECTS = 10;
	static int MAX_TOP_OBJECTS = 100;
	
	public static void main(String[] args) throws IOException, URISyntaxException
	{
		//String host = "10.15.0.144";
		//String host = "192.168.0.145";
		//String host = "ws24348.avicomp.com";
		String host = "localhost";
		List<String> endpointsMin = Arrays.asList(
				 "http://" + host + ":8890/sparql",
				 "http://" + host + ":8891/sparql",
				 "http://" + host + ":8892/sparql",
				 "http://" + host + ":8893/sparql",
				 "http://" + host + ":8894/sparql",
				 "http://" + host + ":8895/sparql",
				 "http://" + host + ":8896/sparql",
				 "http://" + host + ":8897/sparql",
				 "http://" + host + ":8898/sparql"
		);
		
		List<String> endpointsMin2 = Arrays.asList(
				 "http://" + host + ":8890/sparql",
				 "http://" + host + ":8891/sparql",
				 "http://" + host + ":8892/sparql",
				 "http://" + host + ":8893/sparql",
				 "http://" + host + ":8894/sparql",
				 "http://" + host + ":8895/sparql",
				 "http://" + host + ":8896/sparql",
				 "http://" + host + ":8897/sparql",
				 "http://" + host + ":8898/sparql",
				 "http://" + host + ":8899/sparql"
		);
		
		List<String> endpointsMax = Arrays.asList(
			 "http://" + host + ":8890/sparql",
			 "http://" + host + ":8891/sparql",
			 "http://" + host + ":8892/sparql",
			 "http://" + host + ":8893/sparql",
			 "http://" + host + ":8894/sparql",
			 "http://" + host + ":8895/sparql",
			 "http://" + host + ":8896/sparql",
			 "http://" + host + ":8897/sparql",
			 "http://" + host + ":8898/sparql"
			 
			 , "http://" + host + ":8887/sparql"
			 , "http://" + host + ":8888/sparql"
			 , "http://" + host + ":8889/sparql"
			 , "http://" + host + ":8899/sparql"
		);

		List<String> endpointsTest = Arrays.asList(
			   "http://" + host + ":8890/sparql"
			 , "http://" + host + ":8891/sparql"
			 , "http://" + host + ":8892/sparql"
			 //,
				///*
			 //
			 //"http://" + host + ":8893/sparql"
			 //,
			 //"http://" + host + ":8894/sparql"

			 //,
			 //"http://" + host + ":8895/sparql"
			 //,
			 //"http://" + host + ":8896/sparql"
			 //,
			 //*/
			 //"http://" + host + ":8897/sparql"
			 //,
			 ///*
			 //"http://" + host + ":8898/sparql"
			 //,
			 //"http://" + host + ":8899/sparql"
			 //*/
		);
		
		List<String> endpointsExt = Arrays.asList(
		        "http://" + host + ":8887/sparql"
		);
		
		List<String> endpoints = endpointsExt;
		//List<String> endpoints = endpointsMin2;
		//String outputFile = "summaries/sumX-localhost5.n3";
		//String outputFile = "summaries/sum-localhost.n3";
		String outputFile = "summaries/sum-localhost_ext.n3";
		//String namedGraph = "http://aksw.org/fedbench/";  //can be null. in that case all graph will be considered 
		String namedGraph = null;
		TBSSSummariesGenerator generator = new TBSSSummariesGenerator(outputFile);
		long startTime = System.currentTimeMillis();
		int branchLimit = 4;
		generator.generateSummaries(endpoints, namedGraph, branchLimit);
		//generator.generateDAWSummaries(endpoints, namedGraph, branchLimit, 0.5);
		log.info("Data Summaries Generation Time (min): " + (double)(System.currentTimeMillis() - startTime) / (1000 * 60));
		log.info("Data Summaries are secessfully stored at " + outputFile);

		//	outputFile = "summaries\\quetzal-b2.n3";
		//	generator = new SummariesGenerator(outputFile);
		//	startTime = System.currentTimeMillis();
		//	branchLimit =2;
		//	generator.generateSummaries(endpoints,namedGraph,branchLimit);
		//	System.out.println("Data Summaries Generation Time (sec): "+ (System.currentTimeMillis()-startTime)/1000);
		//	System.out.print("Data Summaries are secessfully stored at "+ outputFile);
		//	
		//	outputFile = "summaries\\quetzal-b5.n3";
		//	generator = new SummariesGenerator(outputFile);
		//	startTime = System.currentTimeMillis();
		//	branchLimit =5;
		//	generator.generateSummaries(endpoints,namedGraph,branchLimit);
		//	System.out.println("Data Summaries Generation Time (sec): "+ (System.currentTimeMillis()-startTime)/1000);
		//	System.out.print("Data Summaries are secessfully stored at "+ outputFile);
		//	
		//	outputFile = "summaries\\quetzal-b10.n3";
		//	generator = new SummariesGenerator(outputFile);
		//	startTime = System.currentTimeMillis();
		//	branchLimit =10;
		//	generator.generateSummaries(endpoints,namedGraph,branchLimit);
		//	System.out.println("Data Summaries Generation Time (sec): "+ (System.currentTimeMillis()-startTime)/1000);
		//	System.out.print("Data Summaries are secessfully stored at "+ outputFile);
	}
	
	ExecutorService executorService;
	List<Future<?>> tasks = new ArrayList<Future<?>>();
	
	Future<?> addTask(Runnable task) {
		Future<?> future = null;
		synchronized (executorService) {
			future = executorService.submit(task);
			tasks.add(future);
		}
		return future;
	}
	
	<T> Future<T> addTask(Callable<T> task) {
		Future<T> future = null;
		synchronized (executorService) {
			future = executorService.submit(task);
			tasks.add(future);
		}
		return future;
	}
	
	void waitForTasks() {
		Future<?> future = null;
		while (true) {
			synchronized (executorService) {
				if (tasks.isEmpty()) return;
				future = tasks.get(0);
			}
			try {
				future.get();
			} catch (Exception e) {
    			log.error("", e);
			}
			synchronized (executorService) {
				tasks.remove(0);
			}
		}
	}
	/**
	 * Build Quetzal data summaries for the given list of SPARQL endpoints
	 * @param endpoints List of SPARQL endpoints url
	 * @param graph Named graph. Can be null. In this case all named graphs will be considered for Quetzal summaries
	 * @param branchLimit Branching limit
	 * @throws IOException IO Error
	 */
	public void generateSummaries(List<String> endpoints, String graph, int branchLimit) throws IOException
	{
		executorService = Executors.newFixedThreadPool(16);
		AtomicInteger dsnum = new AtomicInteger(0);
		for (String endpoint : endpoints)
		{
			addTask(new Runnable() {
			    public void run() {
			    	try {
				    	String sum = generateSummary(endpoint, graph, branchLimit, dsnum.incrementAndGet());
				    	
				    	synchronized(bwr) {
				    		try {
				    			bwr.append(sum);
				    			bwr.flush();
				    		} catch (Exception e) {
				    			log.error("", e);
				    		}
				    	}
			    	} catch (Exception e) {
			    		log.error("", e);
			    	}
			    }
			});
		}
		waitForTasks();
		executorService.shutdown();
		bwr.close();
	}
	
	public String generateSummary(String endpoint, String graph, int branchLimit, int dsnum) throws Exception
	{
		long totalTrpl = 0;
		log.info("getting distinct subject count");
		long totalSbj = getDistinctSubjectCount(endpoint);
		log.info("total distinct subjects: "+ totalSbj + " for endpoint: " + endpoint);
		long totalObj = getDistinctObjectCount(endpoint);
		log.info("total distinct objects: "+ totalObj + " for endpoint: " + endpoint);
		List<String> lstPred = getPredicates(endpoint, graph);
        log.info("total distinct predicates: "+ lstPred.size() + " for endpoint: " + endpoint);
        
		StringBuilder sb = new StringBuilder();
		
		sb.append("#---------------------"+endpoint+" Summaries-------------------------------\n");
		sb.append("[] a ds:Service ;\n");
		sb.append("     ds:url   <"+endpoint+"> ;\n");
		
		List<Future<Tuple4<String, Long, Long, Long>>> subtasks = new ArrayList<Future<Tuple4<String, Long, Long, Long>>>();
		
		for (int i = 0; i < lstPred.size(); i++)
		{
			final String predicate = lstPred.get(i);
			if (!verifyIRI(predicate)) {
				subtasks.add(null);
				continue;
			}
			
			Future<Tuple4<String, Long, Long, Long>> statfuture = addTask(new Callable<Tuple4<String, Long, Long, Long>>() {
				@Override
				public Tuple4<String, Long, Long, Long> call() throws Exception {
					return writePrefixes(predicate, endpoint, graph, branchLimit);
				}
			});
			subtasks.add(statfuture);
		}
		
		for (int i = 0; i < lstPred.size(); i++)
		{
			if (subtasks.get(i) == null) continue;
			final String predicate = lstPred.get(i);
			
			StringBuilder tsb = new StringBuilder();
			try {
				tsb.append("     ds:capability\n");
				tsb.append("         [\n");
				tsb.append("           ds:predicate  <" + predicate + "> ;");
				//long distinctSbj =
				
				// sbjs, objs, total
				
				Tuple4<String, Long, Long, Long> stat = subtasks.get(i).get();
				log.info((i+1)+" from " + lstPred.size() + " done: " + predicate + ", endpoint: " + endpoint);
				
				tsb.append(stat.getValue0());
				long distinctSbj = stat.getValue1();
				long distinctObj = stat.getValue2();
				long tripleCount = stat.getValue3();
				
				//long tripleCount2 = getTripleCount(lstPred.get(i), endpoint);
//				if (distinctSbj == 0) {
//					distinctSbj = tripleCount;
//				}
//				if (distinctObj == 0) {
//					distinctObj = tripleCount;
//				}
				tsb.append("           ds:distinctSbjs " + distinctSbj + " ;\n");
				//tsb.append("\n           ds:avgSbjSelectivity  " + (1 / (double)distinctSbj) + " ;");
				
				//writeObjPrefixes(lstPred.get(i), endpoint, graph, branchLimit, tsb);
				//double distinctObj = getObj(lstPred.get(i), endpoint);
				tsb.append("           ds:distinctObjs  " + distinctObj + " ;\n");
				//tsb.append("\n           ds:avgObjSelectivity  " + (1 / (double)distinctObj) + " ;\n");
				
				tsb.append("           ds:triples    " + tripleCount + " ;\n");
				tsb.append("         ] ;\n");
				sb.append(tsb.toString());
				totalTrpl += tripleCount;
			} catch (Exception e) {
				e.printStackTrace();
			}
			
			//totalSbj += distinctSbj;
			//totalObj += (long)distinctObj ;
			
		}
		

		sb.append("     ds:totalSbj "+totalSbj+" ; \n");  // this is not representing the actual number of distinct subjects in a datasets since the same subject URI can be shaared by more than one predicate. but we keep this to save time.  
		sb.append("     ds:totalObj "+totalObj+" ; \n");  
		sb.append("     ds:totalTriples "+totalTrpl+" ; \n");
		sb.append("             .\n");

		//     bw.append("     sd:totalTriples \""+totalTrpl+"\" ;");
		//bw.append("#---------End---------");
		//bw.close();
		return sb.toString();
	}

	/**
	 * Build Duplicate-aware Quetzal data summaries for the given list of SPARQL endpoints
	 * @param endpoints List of SPARQL endpoints url
	 * @param graph Named graph. Can be null. In this case all named graphs will be considered for Quetzal summaries
	 * @param branchLimit Branching limit
	 * @param d Size of MIPS vector can be fixed, e.g., 64 or in percentage, e.g. 0.10 mean the size is the 10% of the ds:triples in dataset capabilities 
	 * @throws IOException Io Error
	 * @throws QueryEvaluationException Query Execution Error 
	 * @throws MalformedQueryException  Memory Error
	 * @throws RepositoryException  Repository Error
	 */
	/*
	public void generateDAWSummaries(String endpoint, String graph, int branchLimit, double d, int dsnum) throws IOException
	{
		StringBuilder sb = new StringBuilder();

		long totalTrpl = 0, totalSbj = 0, totalObj = 0;
		String aMIPsV = "";
		List<String> lstPred = getPredicates(endpoint, graph);
		log.info("total distinct predicates: "+ lstPred.size() + " for endpoint: " + endpoint);
		sb.append("#---------------------" + endpoint + " Summaries-------------------------------\n");

		sb.append("[] a ds:Service ;\n");
		sb.append("     ds:url   <"+endpoint+"> ;\n");
		for (int i = 0; i < lstPred.size(); i++)
		{
			log.info((i+1)+" in progress: " + lstPred.get(i) + ", endpoint: " + endpoint);
			sb.append("     ds:capability\n");
			sb.append("         [\n");
			sb.append("           ds:predicate  <"+lstPred.get(i)+"> ;\n");
			aMIPsV = getMIPsV(lstPred.get(i), endpoint, d);
			sb.append("\n           ds:MIPv       \"" + aMIPsV + "\" ;");
			long distinctSbj = writeSbjPrefixes(lstPred.get(i), endpoint, graph, branchLimit, sb);
			long trpleCount = getTripleCount(lstPred.get(i),endpoint);
			if (distinctSbj == 0) {
				distinctSbj = trpleCount;
			}
			sb.append("\n           ds:avgSbjSelectivity  "+ (1 / (double)distinctSbj)+" ;");
			totalSbj = (long) (totalSbj+distinctSbj);
			writeObjPrefixes(lstPred.get(i), endpoint, graph, branchLimit, sb);
			double distinctObj = getObj(lstPred.get(i),endpoint);
			sb.append("\n           ds:avgObjSelectivity  "+ (1 / distinctObj)+" ;\n");
			totalObj = (long) (totalObj+distinctObj);
			sb.append("           ds:triples    "+trpleCount+" ;");
			sb.append("         ] ;\n");
			totalTrpl = totalTrpl+trpleCount;
		}
		sb.append("     ds:totalSbj "+totalSbj+" ; \n");  // this is not representing the actual number of distinct subjects in a datasets since the same subject URI can be shaared by more than one predicate. but we keep this to save time.  
		sb.append("     ds:totalObj "+totalObj+" ; \n");  
		sb.append("     ds:totalTriples "+totalTrpl+" ; \n\n");
		sb.append("             .\n");
		//     bw.append("     sd:totalTriples \""+totalTrpl+"\" ;");
	}
	*/
	/**
	 * Get total number of triple for a predicate
	 * @param pred Predicate
	 * @param m model
	 * @return triples
	 * @throws RepositoryException 
	 * @throws MalformedQueryException 
	 * @throws QueryEvaluationException 
	 */
	public static double getObj(String pred, String endpoint) throws RepositoryException, MalformedQueryException, QueryEvaluationException {
		String strQuery = "SELECT  (COUNT(DISTINCT ?o) AS ?objs) " + // 
				"WHERE " +
				"{" +
	       		"?s <"+pred+"> ?o " +
	       		"} " ;
		SPARQLRepository repo = createSPARQLRepository(endpoint);
		RepositoryConnection conn = repo.getConnection();
		try {
			TupleQuery query = conn.prepareTupleQuery(QueryLanguage.SPARQL, strQuery); 
			TupleQueryResult rs = query.evaluate();
			return Long.parseLong(rs.next().getValue("objs").stringValue());
		} finally {
			conn.close();
		}
	}
	
	/**
	 * Get total number of distinct subjects of a dataset
	 * @return count 
	 */
	public static Long getSubjectsCount(String endpoint) {
		String strQuery = "SELECT  (COUNT(DISTINCT ?s) AS ?sbjts) " + // 
				"WHERE " +
				"{" +
	       		"?s ?p ?o " +
	       		"} " ;
		SPARQLRepository repo = createSPARQLRepository(endpoint);
		RepositoryConnection conn = repo.getConnection();
		try {
			TupleQuery query = conn.prepareTupleQuery(QueryLanguage.SPARQL, strQuery); 
			TupleQueryResult rs = query.evaluate();
			return Long.parseLong(rs.next().getValue("sbjts").stringValue());
		} finally {
			conn.close();
		}
	}
	/**
	 * Get total number of distinct objects of a dataset
	 * @return count
	 * @throws RepositoryException 
	 * @throws MalformedQueryException 
	 * @throws QueryEvaluationException 
	 */
	public static Long getObjectsCount(String endpoint) throws RepositoryException, MalformedQueryException, QueryEvaluationException {
		long count = 0;
		String strQuery = "SELECT  (COUNT(DISTINCT ?o) AS ?objts) " + // 
				"WHERE " +
				"{" +

	       		"?s ?p ?o " +
	       		"} " ;
		SPARQLRepository repo = createSPARQLRepository(endpoint);
		TupleQuery query = repo.getConnection().prepareTupleQuery(QueryLanguage.SPARQL, strQuery); 
		TupleQueryResult rs = query.evaluate();
		while( rs.hasNext() ) 
		{
			count = Long.parseLong(rs.next().getValue("objts").stringValue());

		}
		rs.close();
		return count;
	}
	/**
	 * Get total number of triple for a predicate
	 * @param pred Predicate
	 * @param m model
	 * @return triples
	 */
	public static Long getTripleCount(String pred, String endpoint) {
		String strQuery = "SELECT  (COUNT(*) AS ?triples) " + // 
				"WHERE " +
				"{" +
	       		"?s <"+pred+"> ?o " +
	       		"} " ;
		SPARQLRepository repo = createSPARQLRepository(endpoint);
		RepositoryConnection conn = repo.getConnection();
		try {
			TupleQuery query = conn.prepareTupleQuery(QueryLanguage.SPARQL, strQuery); 
			TupleQueryResult rs = query.evaluate();
			String v = rs.next().getValue("triples").stringValue();
			rs.close();
			return Long.parseLong(v);
		} finally {
			conn.close();
		}
	}
	
	public static Long getDistinctSubjectCount(String endpoint) {
		String strQuery = "SELECT  (COUNT(distinct ?s) AS ?triples) " + // 
				"WHERE " +
				"{" +
	       		"?s ?p ?o " +
	       		"} " ;
		SPARQLRepository repo = createSPARQLRepository(endpoint);
		RepositoryConnection conn = repo.getConnection();
		try {
			TupleQuery query = conn.prepareTupleQuery(QueryLanguage.SPARQL, strQuery); 
			TupleQueryResult rs = query.evaluate();
			String v = rs.next().getValue("triples").stringValue();
			rs.close();
			return Long.parseLong(v);
		} finally {
			conn.close();
		}
	}
	
	public static Long getDistinctObjectCount(String endpoint) {
		String strQuery = "SELECT  (COUNT(distinct ?o) AS ?triples) " + // 
				"WHERE " +
				"{" +
	       		"?s ?p ?o " +
				"FILTER isIRI(?o)" +
	       		"} " ;
		SPARQLRepository repo = createSPARQLRepository(endpoint);
		RepositoryConnection conn = repo.getConnection();
		try {
			TupleQuery query = conn.prepareTupleQuery(QueryLanguage.SPARQL, strQuery); 
			TupleQueryResult rs = query.evaluate();
			String v = rs.next().getValue("triples").stringValue();
			rs.close();
			return Long.parseLong(v);
		} finally {
			conn.close();
		}
	}
	
	/**
	 * Get all leaf branches of a the each of the URI
	 * @param authGroups List of URIs grouped by same authority
	 * @param branchLimit Branching limit
	 * @return URIs
	 */
	public static SortedSet<String> getAllBranchingURIs(Map<String, List<String>> authGroups, int branchLimit) {
		SortedSet<String> uris = new TreeSet<String>();
		for (List<String> uRIs : authGroups.values())
		{
			//if(auth.equals("http://sdow2008.semanticweb.org/"));
			//  	System.out.println(uRIs);
			TrieNode root = Trie.constructTrie(uRIs, branchLimit);
			uris.addAll(Trie.getRoot2StopingNodePaths(root, branchLimit)); // union
			//System.out.println("Authority: "+auth+", LCP:"+lcp);
		}
		return uris;
	}
	
	/**
	 * Write all the distinct subject prefixes  for triples with predicate p. 
	 * @param predicate  Predicate
	 * @param endpoint Endpoint URL
	 * @param graph named Graph
	 * @param branchLimit Branching Limit for Trie
	 * @throws IOException  IO Error
	 */
	public Tuple4<String, Long, Long, Long> writePrefixes(String predicate, String endpoint, String graph, int branchLimit) throws IOException {
		StringBuilder sb = new StringBuilder();
		
		long limit = 1000000;
		boolean isTypePredicate = predicate.equals("http://www.w3.org/1999/02/22-rdf-syntax-ns#type");

		long rsCount = 0;
		long uniqueSbj = 0;
		long uniqueObj = 0;

		Trie2.Node rootSbj = Trie2.initializeTrie();
		Trie2.Node rootObj = Trie2.initializeTrie();

		SPARQLRepository repo = createSPARQLRepository(endpoint);

		long top = 0;
		
		long rc;
		do
		{
			rc = 0;
			StringBuilder qb = new StringBuilder();
			qb.append("SELECT ?s (count(?o) as ?oc)");
			if (null != graph) {
				qb.append(" FROM <").append(graph).append('>');
			}
			qb.append(" WHERE { ?s <").append(predicate).append("> ?o. } GROUP BY ?s LIMIT ").append(limit).append(" OFFSET ").append(top);
			
			RepositoryConnection conn = repo.getConnection();
			try {
				TupleQuery query = conn.prepareTupleQuery(QueryLanguage.SPARQL, qb.toString()); 
				TupleQueryResult res = query.evaluate();
				
				while (res.hasNext()) 
				{
					++rc;
					BindingSet bs = res.next();
					Value curSbj = bs.getValue("s");
					++uniqueSbj;
					if (verifyIRI(curSbj)) {
						putIRI(curSbj.stringValue(), Long.parseLong(bs.getValue("oc").stringValue()), rootSbj);
					}
				}
				res.close();
			} finally {
				conn.close();
			}
			top += rc;
		} while (rc == limit);
		

		top = 0;
		do
		{
			rc = 0;
			StringBuilder qb = new StringBuilder();
			qb.append("SELECT ?o (count(?s) as ?sc)");
			if (null != graph) {
				qb.append(" FROM <").append(graph).append('>');
			}
			qb.append(" WHERE { ?s <").append(predicate).append("> ?o. } GROUP BY ?o LIMIT ").append(limit).append(" OFFSET ").append(top);
			
			RepositoryConnection conn = repo.getConnection();
			try {
				TupleQuery query = conn.prepareTupleQuery(QueryLanguage.SPARQL, qb.toString()); 
				TupleQueryResult res = query.evaluate();
				
				while (res.hasNext()) 
				{
					++rc;
					BindingSet bs = res.next();
					Value curObj = bs.getValue("o");
					++uniqueObj;
					if (verifyIRI(curObj)) {
						putIRI(curObj.stringValue(), Long.parseLong(bs.getValue("sc").stringValue()), rootObj);
					}
				}
				res.close();
			} finally {
				conn.close();
			}
			top += rc;
		} while (rc == limit);

		
		rsCount = getTripleCount(predicate, endpoint);
		
		boolean first = true;
		sb.append("\n           ds:topSbjs");
		List<Pair<String, Long>> topsbjstotal = Trie2.findMostHittable(rootSbj, 1000 > MAX_TOP_OBJECTS ? 1000 : MAX_TOP_OBJECTS);
		List<Pair<String, Long>> topsbjs = new ArrayList<Pair<String, Long>>();
		List<String> middlesbjs = new ArrayList<String>();
		long avrmiddlesbjcard = doSaleemAlgo(MIN_TOP_OBJECTS, MAX_TOP_OBJECTS, topsbjstotal, topsbjs, middlesbjs);
		for (Pair<String, Long> p : topsbjs) {
			if (!first) sb.append(","); else first = false;
			sb.append("\n             [ ds:subject <").append(makeWellFormed(p.getFirst())).append(">; ds:card ").append(p.getSecond()).append(" ]");
		}
		if (!middlesbjs.isEmpty()) {
			sb.append(",\n             [ ds:middle ");
			first = true;
			for (String ms : middlesbjs) {
				if (!first) sb.append(","); else first = false;
				sb.append('<').append(makeWellFormed(ms)).append('>');
			}
			sb.append("; ds:card ").append(avrmiddlesbjcard).append(" ]");
		}
		if (topsbjs.isEmpty()) sb.append(" []");
		
		first = true;
		sb.append(";\n           ds:topObjs");

		List<Pair<String, Long>> topobjstotal = Trie2.findMostHittable(rootObj, isTypePredicate ? Integer.MAX_VALUE : (1000 > MAX_TOP_OBJECTS ? 1000 : MAX_TOP_OBJECTS));
		List<Pair<String, Long>> topobjs = null;
		List<String> middleobjs = new ArrayList<String>();
		long avrmiddleobjcard = 0;
		if (!isTypePredicate) {
			topobjs = new ArrayList<Pair<String, Long>>();
			avrmiddleobjcard = doSaleemAlgo(MIN_TOP_OBJECTS, MAX_TOP_OBJECTS, topobjstotal, topobjs, middleobjs);
		} else {
			topobjs = topobjstotal;
		}
		for (Pair<String, Long> p : topobjs) {
			if (!first) sb.append(","); else first = false;
			sb.append("\n             [ ds:object <").append(makeWellFormed(p.getFirst())).append(">; ds:card ").append(p.getSecond()).append(" ]");
		}
		if (!middleobjs.isEmpty()) {
			sb.append(",\n             [ ds:middle ");
			first = true;
			for (String ms : middleobjs) {
				if (!first) sb.append(","); else first = false;
				sb.append('<').append(makeWellFormed(ms)).append('>');
			}
			sb.append("; ds:card ").append(avrmiddleobjcard).append(" ]");
		}
		if (topobjs.isEmpty()) sb.append(" []");
		
		first = true;
		sb.append(";\n           ds:subjPrefixes");
		List<Tuple3<String, Long, Long>> sprefs = Trie2.gatherPrefixes(rootSbj, branchLimit);
		for (Tuple3<String, Long, Long> t : sprefs) {
			if (!first) sb.append(","); else first = false;
			sb.append("\n             [ ds:prefix \"").append(encodeStringLiteral(t.getValue0())).append("\"; ds:unique ").append(t.getValue1()).append("; ds:card ").append(t.getValue2()).append(" ]");
		}
		if (sprefs.isEmpty()) sb.append(" []");
		
		first = true;
		sb.append(";\n           ds:objPrefixes");
		if (!isTypePredicate) {
			List<Tuple3<String, Long, Long>> oprefs = Trie2.gatherPrefixes(rootObj, branchLimit);
			for (Tuple3<String, Long, Long> t : oprefs) {
				if (!first) sb.append(","); else first = false;
				sb.append("\n             [ ds:prefix \"").append(encodeStringLiteral(t.getValue0())).append("\"; ds:unique ").append(t.getValue1()).append("; ds:card ").append(t.getValue2()).append(" ]");
			}
			if (oprefs.isEmpty()) sb.append(" []");
		} else {
			sb.append(" []");
		}
		
		sb.append(";\n");
		//log.info("subject: " + topsbjs);
		//log.info("object: " + topobjs);
		
		return new Tuple4<String, Long, Long, Long>(sb.toString(), uniqueSbj, uniqueObj, rsCount);
	}
	
	///**
	// * Get a SPARQL query to retrieve all the object authorities for a predicate
	// * Note: Due to a limit of 10000 results per query on a SPARQL endpoint, we are using Regular expressions in queries
	// * to get the required part in each qualifying triples rather than doing a local SPLIT operation on results. For
	// * rdf:type we retrieve the complete set of objects as usually the number of distinct classes in a dataset is usually not too many.
	// * @param predicate Predicate
	// * @return query Required SPARQL query
	// */
	//public String getObjAuthorityQury(String predicate) {
	//	String query;
	//	if (predicate.equals("http://www.w3.org/1999/02/22-rdf-syntax-ns#type"))
	//	{
	//		 query = "SELECT DISTINCT ?authPath From <http://deri.benchmark> \n"
	//				+ "WHERE \n"
	//				+ "{  \n"
	//				+ "   ?s <"+predicate+"> ?authPath. \n"
	//			
	//						+ "}" ;
	//	}
	//	
	//	else
	//	{
	//	 query = "SELECT DISTINCT ?authPath From <http://deri.benchmark> \n"
	//			+ "WHERE \n"
	//			+ "{  \n"
	//			+ "   ?s <"+predicate+"> ?o. \n"
	//			+ "  BIND(STRBEFORE(str(?o),REPLACE(str(?o), \"^([^/]*/){3}\", \"\")) AS ?authPath) \n "
	//					+ "   Filter(isURI(?o)) \n"
	//					+ "}" ;
	//	}
	//		return query;
	//}

	/**
	 *  Get a SPARQL query to retrieve all distinct objects for retrieving all distinct object authorities for a predicate
	 * Note: You need to increase the 1000 limit of results for SPARQL endpoints if the distinct subjects for a predicate is greather than that limit
	 * @param predicate Predicate
	 * @param graph Named graph
	 * @return query Required SPARQL query
	 */
	public String getObjAuthorityQury(String predicate, String graph) {
		StringBuilder sb = new StringBuilder();
		sb.append("SELECT DISTINCT ?o");
		if (null != graph) {
			sb.append(" FROM <");
			sb.append(graph);
			sb.append(">");
		}
		sb.append(" WHERE { ?s <");
		sb.append(predicate);
		sb.append("> ?o. FILTER(isURI(?o)) }");

		return sb.toString();
	}
	
	//-----------------------Return Mean wise independent permutation vector (MIPsV) for a predicate-------------	
	/**
	 * Generate Mean wise independent permutation vector (MIPsV) for a predicate
	 * @param pred Predicate name
	 * @param endpoint SPARQL endpoint URL
	 * @param d MipsVector Size can be fixed  e.g. 64 or in percentage e.g., 0.10 means 10%
	 * @return MIPsV Mips Vector
	 * @throws RepositoryException 
	 * @throws MalformedQueryException 
	 * @throws QueryEvaluationException 
	 */
	private String getMIPsV(String pred, String endpoint, double d) throws IOException
	{
		ArrayList<Long> idsVector = new ArrayList<Long>() ;
		String MIPsV = "";
		String strQuery = getMIPsVQury(pred);
		SPARQLRepository repo = createSPARQLRepository(endpoint);
		TupleQuery query = repo.getConnection().prepareTupleQuery(QueryLanguage.SPARQL, strQuery); 
		TupleQueryResult rs = query.evaluate();
		while( rs.hasNext() ) 
		{
			BindingSet bset = rs.next();
			String sbj_obj = bset.getBinding("s").getValue().toString().concat(bset.getBinding("o").getValue().toString());
			idsVector.add((long) (sbj_obj.hashCode()));
		}
		long trplCount = idsVector.size();
		Collection c = new ArrayCollection(idsVector);
		MIPsynopsis synMIPs = null;
		if (d >= 1) {
			synMIPs = new MIPsynopsis(c, (int)d, 242); 
		} else {
		    synMIPs = new MIPsynopsis(c, (int)(Math.ceil(trplCount*d)), 242); 
		}
		long[] minValues = synMIPs.minValues;
		for (int i=0; i<minValues.length; i++)
			MIPsV = MIPsV.concat(minValues[i]+" ");

		return MIPsV.trim();
	}
	
	//--------------------------------------------------------------------------
	/**
	 * Get query for MIPs Vectory generation
	 * @param pred Predicate name for which MIPs vector is required
	 */
	private static String getMIPsVQury(String pred) 
	{
		String MIPsVQuery = "SELECT   ?s  ?o " + // 
				"WHERE " +
				"{" +

				               		"?s <"+pred+"> ?o " +
				               		"} " ;
		return MIPsVQuery;
	}

	/**
	 * Get Predicate List
	 * @param endPointUrl SPARQL endPoint Url
	 * @param graph Named graph
	 * @return  predLst Predicates List
	 */
	private static List<String> getPredicates(String endPointUrl, String graph)
	{
		List<String>  predLst = new ArrayList<String>();
		String strQuery = getPredQury(graph);
		SPARQLRepository repo = createSPARQLRepository(endPointUrl);
		RepositoryConnection conn = repo.getConnection();
		try {
			TupleQuery query = conn.prepareTupleQuery(QueryLanguage.SPARQL, strQuery); 
			TupleQueryResult res = query.evaluate();
			while (res.hasNext()) 
			{
				String pred = res.next().getValue("p").toString();
				predLst.add(pred);	  		
			}
			res.close();
		} finally {
			conn.close();
		}
		return predLst;
	}

	//--------------------------------------------------------------------------
	/**
	 * Get SPARQL query to retrieve all predicates in a SAPRQL endpoint
	 * @param graph Named Graph
	 * @return query SPARQL query
	 */
	private static String getPredQury(String graph) {
		StringBuilder sb = new StringBuilder();
		sb.append("SELECT DISTINCT ?p");
		if (null != graph) {
			sb.append(" FROM <");
			sb.append(graph);
			sb.append(">");
		}
		sb.append(" WHERE { ?s ?p ?o }");
		return sb.toString();
	}
	
	/**
	 * 
	 * 
	 * @param objects cardinality ordered list of objects
	 * @param top output collection of top objects
	 * @param middle collection of top objects
	 * @return average cardinality
	 */
	long doSaleemAlgo(int min, int max, List<Pair<String, Long>> objects, List<Pair<String, Long>> top, List<String> middle) {
		while (!objects.isEmpty() && objects.get(objects.size() - 1).getSecond() == 1) {
			objects.remove(objects.size() - 1);
		}
			
		if (min > objects.size()) min = objects.size();
		
		for (int i = 0; i < min; ++i) {
			Pair<String, Long> obj = objects.get(i);
			top.add(obj);
		}
		
		int max2 = max < objects.size() ? max : objects.size();

		// find first diff maximum
		long maxdiff = 0;
		int maxdiffidx = -1;
		for (int i = min; i < max2 - 1; ++i) {
			long diff = objects.get(i).getSecond() - objects.get(i + 1).getSecond();
			if (diff > maxdiff) {
				maxdiff = diff;
				maxdiffidx = i;
			}
		}
		if (maxdiffidx == -1) return 0;
		// copy objects
		for (int i = min; i < maxdiffidx; ++i) {
			Pair<String, Long> obj = objects.get(i);
			top.add(obj);
		}
		
		// find next diff maximum
		maxdiff = 0;
		int nextmaxdiffidx = -1;
		for (int i = maxdiffidx + 1; i < max2 - 1; ++i) {
			long diff = objects.get(i).getSecond() - objects.get(i + 1).getSecond();
			if (diff > maxdiff) {
				maxdiff = diff;
				nextmaxdiffidx = i;
			}
		}
		if (nextmaxdiffidx == -1) {
			nextmaxdiffidx = max2;
		}
		if (maxdiffidx == nextmaxdiffidx) return 0;
		
		// copy middle objects
		long totalCard = 0;
		for (int i = maxdiffidx; i < nextmaxdiffidx; ++i) {
			Pair<String, Long> obj = objects.get(i);
			middle.add(obj.getFirst());
			totalCard += obj.getSecond();
		}
		
		return totalCard / (nextmaxdiffidx - maxdiffidx);
	}
}