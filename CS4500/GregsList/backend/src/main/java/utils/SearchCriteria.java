package utils;

import models.Service;
import java.util.List;

public class SearchCriteria {

  private List<SearchPredicate> searchPredicates;
  private Service service;

  public SearchCriteria(List<SearchPredicate> searchPredicates, Service service) {
    this.searchPredicates = searchPredicates;
    this.service = service;
  }

  public List<SearchPredicate> getSearchPredicates() {
    return this.searchPredicates;
  }

  public void setSearchPredicates(List<SearchPredicate> searchPredicates) {
    this.searchPredicates = searchPredicates;
  }

  public Service getService() {
    return this.service;
  }

  public void setService(Service service) {
    this.service = service;
  }
}
