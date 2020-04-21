import apiFetch, {
  deleteRequest,
  postJson,
  putRequest,
} from '../util/apiFetch';

export default class FAQService {
  static instance = null;

  static getInstance() {
    if (FAQService.instance === null) {
      FAQService.instance = new FAQService();
    }
    return this.instance;
  }

  findFAQById = id =>
    apiFetch(`/api/faqs/${id}`).then(response => response.json());

  findAllFrequentlyAskedQuestions = (currentPage, perPage, title, question) =>
    apiFetch(
      `/api/faqs?page=${currentPage}&count=${perPage}&titleFilter=${title}&questionFilter=${question}`
    ).then(response => response.json());

  // Data should have a title and question
  createFAQ = data =>
    postJson('/api/faqs', data).then(response => response.json());

  updateFAQ = (id, data) =>
    putRequest(`/api/faqs/${id}`, data).then(response => response.json());

  deleteFAQ = id => deleteRequest(`/api/faqs/${id}`);
}
