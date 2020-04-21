import java.util.Arrays;
import java.util.Collections;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

import models.Service;
import models.ServiceAnswer;
import models.ServiceQuestion;
import models.User;
import utils.SearchCriteria;
import utils.SearchPredicate;
import utils.ServiceSearch;
import java.util.ArrayList;
import java.util.List;

public class ServiceSearchTest {
    private Service service;
    private SearchCriteria searchCriteria;
    private ServiceSearch serviceSearch;
    private User providerA;
    private User providerB;
    private User providerC;
    private ServiceQuestion sq1;
    private ServiceQuestion sq2;

    @BeforeEach
    void beforeEach() {
        service = new Service(null, "House Cleaning", 0, null, null);

        // service questions for service
        sq1 = new ServiceQuestion("How many rooms?", "Range", "0,100", null, null);
        sq2 = new ServiceQuestion("Have pets?", "TrueFalse", "true,false", null, null);

        // provider A
        providerA = new User();
        ServiceAnswer providerA_answer1 = new ServiceAnswer(null, 2, 3, null, sq1, providerA);
        ServiceAnswer providerA_answer2 = new ServiceAnswer(false, null, null, null, sq2, providerA);
        List<ServiceAnswer> answersOfProviderA = new ArrayList<>(Arrays.asList(providerA_answer1, providerA_answer2));
        providerA.setServiceAnswers(answersOfProviderA);

        // provider B
        providerB = new User();
        ServiceAnswer providerB_answer1 = new ServiceAnswer(null, 3, 4, null, sq1, providerB);
        ServiceAnswer providerB_answer2 = new ServiceAnswer(true, null, null, null, sq2, providerB);
        List<ServiceAnswer> answersOfProviderB = new ArrayList<>(Arrays.asList(providerB_answer1, providerB_answer2));
        providerB.setServiceAnswers(answersOfProviderB);

        // provider C
        providerC = new User();
        ServiceAnswer providerC_answer1 = new ServiceAnswer(null, 4, 5, null, sq1, providerC);
        ServiceAnswer providerC_answer2 = new ServiceAnswer(true, null, null, null, sq2, providerC);
        List<ServiceAnswer> answersOfProviderC = new ArrayList<>(Arrays.asList(providerC_answer1, providerC_answer2));
        providerC.setServiceAnswers(answersOfProviderC);

        // list of all providers with answers
        List<User> allProviders = new ArrayList<>(Arrays.asList(providerA, providerB, providerC));

        // set the providers
        service.setProviders(allProviders);

        // --------------------------------------------------
        // create search criteria

        // first search predicate
        ServiceAnswer saPredicate1 = new ServiceAnswer(null, 3, 3, null, sq1, null);
        SearchPredicate searchPredicate1 = new SearchPredicate(sq1, saPredicate1);

        // second search predicate
        ServiceAnswer saPredicate2 = new ServiceAnswer(true, null, null, null, sq2, null);
        SearchPredicate searchPredicate2 = new SearchPredicate(sq2, saPredicate2);

        List<SearchPredicate> allSearchPredicates = new ArrayList<>(Arrays.asList(searchPredicate1, searchPredicate2));

        // initialize search criteria with all search predicates
        searchCriteria = new SearchCriteria(allSearchPredicates, service);
    }

    @Test
    void testScoresCalculatedCorrectly() {
        int resultForProviderA = ServiceSearch.getScoreForOneProvider(providerA, searchCriteria);
        int resultForProviderB = ServiceSearch.getScoreForOneProvider(providerB, searchCriteria);
        int resultForProviderC = ServiceSearch.getScoreForOneProvider(providerC, searchCriteria);

        assertEquals(resultForProviderA, 1);
        assertEquals(resultForProviderB, 2);
        assertEquals(resultForProviderC, 1);
    }

    @Test
    void testScoreGreaterThanOrEqualToZero() {
        int resultForProviderA = ServiceSearch.getScoreForOneProvider(providerA, searchCriteria);
        int resultForProviderB = ServiceSearch.getScoreForOneProvider(providerB, searchCriteria);
        int resultForProviderC = ServiceSearch.getScoreForOneProvider(providerC, searchCriteria);

        assertTrue(resultForProviderA >= 0);
        assertTrue(resultForProviderB >= 0);
        assertTrue(resultForProviderC >= 0);
    }

    @Test
    void testSameServiceProvidersSameScore() {
        // creating a new provider with the same exact answers as provider A
        User providerD = new User();
        ServiceAnswer provider4_answer1 = new ServiceAnswer(null, 2, 3, null, sq1, providerD);
        ServiceAnswer provider4_answer2 = new ServiceAnswer(false, null, null, null, sq2, providerD);
        List<ServiceAnswer> answersOfProviderD = new ArrayList<>(Arrays.asList(provider4_answer1, provider4_answer2));
        providerD.setServiceAnswers(answersOfProviderD);

        int resultForProviderA = ServiceSearch.getScoreForOneProvider(providerA, searchCriteria);
        int resultForProviderD = ServiceSearch.getScoreForOneProvider(providerD, searchCriteria);

        assertEquals(resultForProviderA, resultForProviderD);
    }

    @Test
    void testSearchServiceReturnsCorrectNumberOfProvidersInCorrectOrder() {
        List<User> providerResults = ServiceSearch.searchForProviders(searchCriteria);
        assertEquals(providerResults.size(), 3);

        assertEquals(providerResults.get(0), providerB);
        assertEquals(providerResults.get(1), providerC);
        assertEquals(providerResults.get(2), providerA);
    }

    @Test
    void testSearchServiceReturnsEmptyListWhenProvidersListIsEmpty() {
        service.setProviders(Collections.EMPTY_LIST);
        List<User> providerResults = ServiceSearch.searchForProviders(searchCriteria);

        assertTrue(providerResults.isEmpty());
    }
}
