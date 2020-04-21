package services;

import models.FrequentlyAskedAnswer;
import models.Service;
import models.ServiceAnswer;
import repositories.FrequentlyAskedAnswerRepository;
import repositories.ServiceAnswerRepository;
import repositories.ServiceRepository;
import utils.SearchCriteria;
import utils.ServiceSearch;
import java.util.List;

import org.springframework.beans.factory.annotation.Autowired;
import org.springframework.web.bind.annotation.DeleteMapping;
import org.springframework.web.bind.annotation.GetMapping;
import org.springframework.web.bind.annotation.PathVariable;
import org.springframework.web.bind.annotation.PostMapping;
import org.springframework.web.bind.annotation.PutMapping;
import org.springframework.web.bind.annotation.RequestBody;
import org.springframework.web.bind.annotation.RestController;
import org.springframework.web.bind.annotation.CrossOrigin;
import org.springframework.web.bind.annotation.RequestParam;
import org.springframework.web.bind.annotation.RequestMapping;
import org.springframework.web.bind.annotation.RequestMethod;

import models.User;
import repositories.UserRepository;

@RestController
@CrossOrigin(origins = "*")
public class UserService {
  @Autowired
  UserRepository userRepository;
  @Autowired
  ServiceRepository serviceRepository;
  @Autowired
  FrequentlyAskedAnswerRepository frequentlyAskedAnswerRepository;
  @Autowired
  ServiceAnswerRepository serviceAnswerRepository;

  @GetMapping("/api/users")
  public List<User> findAllUser() {
    return userRepository.findAllUsers();
  }

  @GetMapping("/api/users/{userId}")
  public User findUserById(@PathVariable("userId") Integer id) {
    return userRepository.findUserById(id);
  }

  @RequestMapping(value = "/api/users/query", method = RequestMethod.GET)
  public User findUserByUsername(@RequestParam("username") String username) {
    User match = userRepository.findByUsername(username);
    return match;
  }

  @PostMapping("/api/users")
  public User createUser(@RequestBody User user) {
    return userRepository.save(user);
  }

  @PostMapping("/api/users/search")
  public List<User> findUsersForSearch(@RequestBody SearchCriteria searchCriteria) {
    int id = searchCriteria.getService().getId();
    Service service = serviceRepository.findServiceById(id);
    searchCriteria.setService(service);
    return ServiceSearch.searchForProviders(searchCriteria);
  }

  @PutMapping("/api/users/{userId}")
  public User updateUser(@PathVariable("userId") Integer id, @RequestBody User userUpdates) {
    User user = userRepository.findUserById(id);
    user.setFirstName(userUpdates.getFirstName());
    user.setLastName(userUpdates.getLastName());
    user.setServiceAnswers(userUpdates.getServiceAnswers());
    user.setFrequentlyAskedAnswers(userUpdates.getFrequentlyAskedAnswers());
    user.setServices(userUpdates.getServices());
    // for provider profile
    user.setTitle(userUpdates.getTitle());
    user.setIntroduction(userUpdates.getIntroduction());
    user.setTimesHired(userUpdates.getTimesHired());
    user.setBusinessCreationDate(userUpdates.getBusinessCreationDate());
    user.setBackgroundChecked(userUpdates.getBackgroundChecked());
    // for business profile
    user.setBusinessYearFounded(userUpdates.getBusinessYearFounded());
    user.setEmployees(userUpdates.getEmployees());
    user.setBusinessEmail(userUpdates.getBusinessEmail());
    user.setBusinessAddressStreet(userUpdates.getBusinessAddressStreet());
    user.setBusinessAddressCity(userUpdates.getBusinessAddressCity());
    user.setBusinessAddressState(userUpdates.getBusinessAddressState());
    user.setBusinessAddressZip(userUpdates.getBusinessAddressZip());
    user.setBusinessPaymentMethods(userUpdates.getBusinessPaymentMethods());
    user.setBusinessFacebookURL(userUpdates.getBusinessFacebookURL());
    user.setBusinessInstagramURL(userUpdates.getBusinessInstagramURL());
    user.setBusinessTwitterURL(userUpdates.getBusinessTwitterURL());

    if (userUpdates.getPassword() != null && !userUpdates.getPassword().equals("")) {
      user.setPassword(userUpdates.getPassword());
    }
    return userRepository.save(user);
  }

  @DeleteMapping("/api/users/{userId}")
  public void deleteUser(@PathVariable("userId") Integer id) {
    userRepository.deleteById(id);
  }

  @GetMapping("/api/users/{userId}/services")
  public List<Service> findServicesByUser(@PathVariable("userId") Integer id) {
    User user = userRepository.findUserById(id);
    return user.getServices();
  }

  @GetMapping("/api/users/{userId}/frequentlyAskedAnswers")
  public List<FrequentlyAskedAnswer> findAllFrequentlyAskedAnswersForUser(@PathVariable("userId") Integer id) {
    return userRepository.findAllFrequentlyAskedAnswersForUser(id);
  }

  @PostMapping("/api/users/{userId}/frequentlyAskedAnswers")
  public User addFrequentlyAskedAnswerForUser(@PathVariable("userId") Integer id,
      @RequestBody FrequentlyAskedAnswer faa) {
    User user = userRepository.findUserById(id);
    List<FrequentlyAskedAnswer> faal = user.getFrequentlyAskedAnswers();
    faal.add(faa);
    user.setFrequentlyAskedAnswers(faal);
    faa.setUser(user);
    frequentlyAskedAnswerRepository.save(faa);
    return userRepository.save(user);
  }

  @PostMapping("/api/users/{userId}/frequentlyAskedAnswers/{faaId}")
  public User addFrequentlyAskedAnswerRelationshipForUser(@PathVariable("userId") Integer uId,
      @PathVariable("faaId") Integer faaId) {
    User user = userRepository.findUserById(uId);
    List<FrequentlyAskedAnswer> faaList = user.getFrequentlyAskedAnswers();
    FrequentlyAskedAnswer faa = frequentlyAskedAnswerRepository.findFrequentlyAskedAnswerById(faaId);
    if (!faaList.contains(faa)) {
      faaList.add(faa);
      user.setFrequentlyAskedAnswers(faaList);
      faa.setUser(user);
    }
    frequentlyAskedAnswerRepository.save(faa);
    return userRepository.save(user);
  }

  @DeleteMapping("/api/users/{userId}/frequentlyAskedAnswers/{faaId}")
  public User removeFrequentlyAskedAnswerRelationshipForUser(@PathVariable("userId") Integer uId,
      @PathVariable("faaId") Integer faaId) {
    User user = userRepository.findUserById(uId);
    FrequentlyAskedAnswer faa = frequentlyAskedAnswerRepository.findFrequentlyAskedAnswerById(faaId);
    List<FrequentlyAskedAnswer> faaList = user.getFrequentlyAskedAnswers();
    if (faaList.contains(faa)) {
      faaList.remove(faa);
      user.setFrequentlyAskedAnswers(faaList);
      faa.setUser(null);
    }
    frequentlyAskedAnswerRepository.save(faa);
    return userRepository.save(user);
  }

  @GetMapping("/api/users/{userId}/serviceAnswers")
  public List<ServiceAnswer> findAllServiceAnswers(@PathVariable("userId") Integer id) {
    return userRepository.findAllServiceAnswersForUser(id);
  }

  @PostMapping("/api/users/{userId}/serviceAnswers")
  public User addServiceAnswerForUser(@PathVariable("userId") Integer id, @RequestBody ServiceAnswer sa) {
    User user = userRepository.findUserById(id);
    List<ServiceAnswer> sal = user.getServiceAnswers();
    sal.add(sa);
    user.setServiceAnswers(sal);
    sa.setProvider(user);
    serviceAnswerRepository.save(sa);
    return userRepository.save(user);
  }

  @PostMapping("/api/users/{userId}/serviceAnswers/{saId}")
  public User addServiceAnswerRelationshipForUser(@PathVariable("userId") Integer uId,
      @PathVariable("saId") Integer saId) {
    User user = userRepository.findUserById(uId);
    List<ServiceAnswer> saList = user.getServiceAnswers();
    ServiceAnswer sa = serviceAnswerRepository.findServiceAnswerById(saId);
    if (!saList.contains(sa)) {
      saList.add(sa);
      user.setServiceAnswers(saList);
      sa.setProvider(user);
    }
    serviceAnswerRepository.save(sa);
    return userRepository.save(user);
  }

  @DeleteMapping("/api/users/{userId}/serviceAnswers/{saId}")
  public User removeServiceAnswerRelationshipForUser(@PathVariable("userId") Integer uId,
      @PathVariable("saId") Integer saId) {
    User user = userRepository.findUserById(uId);
    ServiceAnswer sa = serviceAnswerRepository.findServiceAnswerById(saId);
    List<ServiceAnswer> saList = user.getServiceAnswers();
    if (saList.contains(sa)) {
      saList.remove(sa);
      user.setServiceAnswers(saList);
      sa.setProvider(null);
    }
    serviceAnswerRepository.save(sa);
    return userRepository.save(user);
  }

  @PostMapping("/api/users/{userId}/services/{serviceId}")
  public User createServiceRelationship(@PathVariable("userId") Integer userId,
      @PathVariable("serviceId") Integer serviceId) {
    User user = userRepository.findUserById(userId);
    Service service = serviceRepository.findServiceById(serviceId);
    List<Service> userRelations = user.getServices();
    List<User> serviceRelations = service.getProviders();
    if (!userRelations.contains(service)) {
      userRelations.add(service);
      user.setServices(userRelations);
      serviceRelations.add(user);
      service.setProviders(serviceRelations);
    }
    serviceRepository.save(service);
    return userRepository.save(user);
  }

  @DeleteMapping("/api/users/{userId}/services/{serviceId}")
  public User deleteServiceRelationship(@PathVariable("userId") Integer userId,
      @PathVariable("serviceId") Integer serviceId) {
    User user = userRepository.findUserById(userId);
    Service service = serviceRepository.findServiceById(serviceId);
    List<Service> userRelations = user.getServices();
    List<User> serviceRelations = service.getProviders();
    if (userRelations.contains(service)) {
      userRelations.remove(service);
      user.setServices(userRelations);
      serviceRelations.remove(user);
      service.setProviders(serviceRelations);
    }
    serviceRepository.save(service);
    return userRepository.save(user);
  }
}
