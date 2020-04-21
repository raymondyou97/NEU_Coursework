package utils;

import models.User;
import java.util.Collections;
import java.util.Comparator;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.stream.Collectors;

public class ServiceSearch {

  public static List<User> searchForProviders(SearchCriteria searchCriteria) {
    Map<User, Integer> predicateMatches = new HashMap<>();
    List<User> providers = searchCriteria.getService().getProviders();

    for (User user : providers) {
      // record how many predicate matches this provider had with the search criteria
      predicateMatches.put(user, getScoreForOneProvider(user, searchCriteria));
    }

    // sort the providers by the number of predicate matches
    providers.sort(Comparator.comparing(predicateMatches::get));
    Collections.reverse(providers);

    return providers;
  }

  public static int getScoreForOneProvider(User user, SearchCriteria searchCriteria) {
    int totalMatches = 0;

    // represents the predicates set by the current provider
    List<SearchPredicate> providerPredicates = user.getServiceAnswers().stream()
        .map((answer) -> new SearchPredicate(answer.getServiceQuestion(), answer)).collect(Collectors.toList());

    for (SearchPredicate searchPredicate : searchCriteria.getSearchPredicates()) {
      for (SearchPredicate providerPredicate : providerPredicates) {
        if (searchPredicate.match(providerPredicate)) {
          totalMatches += 1;
          break;
        }
      }
    }

    return totalMatches;
  }
}
